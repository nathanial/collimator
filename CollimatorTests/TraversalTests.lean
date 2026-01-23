import Batteries
import Collimator.Core
import Collimator.Optics
import Collimator.Operators
import Collimator.Concrete.FunArrow
import Collimator.Theorems.TraversalLaws
import Collimator.Combinators
import Collimator.Instances
import Crucible
import Collimator.Control.WriterT

open Collimator.Control (WriterT tell)

/-!
# Traversal Tests

Comprehensive test suite for traversals, including:
- Traversal laws (identity, naturality)
- Basic traversal operations (over, traverse)
- Composed traversals
- Effectful traversals with different applicative functors
- Property-based tests for traversals
-/

namespace CollimatorTests.TraversalTests

open Batteries
open Collimator
open Collimator.Core
open Collimator.Concrete
open Collimator.Theorems
open Collimator.Combinators
open Collimator.Traversal
open Collimator.Fold
open Collimator.Setter
open Collimator.AffineTraversalOps
open Collimator.Instances.List (traversed)
open Crucible
open scoped Collimator.Operators

testSuite "Traversal Tests"

/-! ## Test Structures -/

inductive Tree (α : Type _) where
  | leaf : α → Tree α
  | node : Tree α → Tree α → Tree α
  deriving BEq, Repr

structure Point where
  x : Int
  y : Int
  deriving BEq, Repr, DecidableEq

structure Rectangle where
  topLeft : Point
  bottomRight : Point
  deriving BEq, Repr, DecidableEq

/-! ## Traversal Definitions -/

private def Tree.walkMon {α : Type _} {F : Type _ → Type _} [Applicative F]
    (f : α → F α) : Tree α → F (Tree α)
  | Tree.leaf a => pure Tree.leaf <*> f a
  | Tree.node l r =>
      pure Tree.node <*> Tree.walkMon f l <*> Tree.walkMon f r

private def List.walkMon {α : Type _} {F : Type _ → Type _} [Applicative F]
    (f : α → F α) : List α → F (List α)
  | [] => pure []
  | x :: xs => pure List.cons <*> f x <*> List.walkMon f xs

private def Option.walkMon {α : Type _} {F : Type _ → Type _} [Applicative F]
    (f : α → F α) : Option α → F (Option α)
  | none => pure none
  | some a => pure Option.some <*> f a

/-! ## Lawful Instances -/

instance {α : Type _} : LawfulTraversal (@Tree.walkMon α) where
  traverse_identity := by
    intro x
    induction x with
    | leaf a => rfl
    | node l r ihl ihr =>
      unfold Tree.walkMon
      simp only [ihl, ihr]
      rfl
  traverse_naturality := by
    intro F G _ _ η h_pure h_seq f x
    induction x with
    | leaf a =>
      unfold Tree.walkMon
      rw [h_seq, h_pure]
    | node l r ihl ihr =>
      unfold Tree.walkMon
      rw [h_seq, h_seq, ihl, ihr, h_pure]

instance {α : Type _} : LawfulTraversal (@List.walkMon α) where
  traverse_identity := by
    intro x
    induction x with
    | nil => rfl
    | cons h t ih =>
      unfold List.walkMon
      simp only [ih]
      rfl
  traverse_naturality := by
    intro F G _ _ η h_pure h_seq f x
    induction x with
    | nil =>
      unfold List.walkMon
      simp only [h_pure]
    | cons h t ih =>
      unfold List.walkMon
      rw [h_seq, h_seq, ih]
      simp only [h_pure]

instance {α : Type _} : LawfulTraversal (@Option.walkMon α) where
  traverse_identity := by
    intro x
    cases x <;> rfl
  traverse_naturality := by
    intro F G _ _ η h_pure h_seq f x
    cases x with
    | none =>
      unfold Option.walkMon
      simp only [h_pure]
    | some a =>
      unfold Option.walkMon
      rw [h_seq, h_pure]

/-! ## Lens and Prism Definitions -/

private def pointLens : Lens Point Point Int Int :=
  lens' (fun p => p.x) (fun p x' => { p with x := x' })

private def Point.xLens : Lens' Point Int :=
  lens' (fun p => p.x) (fun p x' => { p with x := x' })

private def Rectangle.topLeftLens : Lens' Rectangle Point :=
  lens' (fun r => r.topLeft) (fun r p => { r with topLeft := p })

private def optionPrism : Prism (Option Int) (Option Int) Int Int :=
  prism (s := Option Int) (t := Option Int) (a := Int) (b := Int)
    (build := Option.some)
    (split := fun | some n => Sum.inr n | none => Sum.inl none)

/-! ## Random Value Generation for Property Tests -/

/-- Generate a pseudo-random Int from a rngSeed -/
private def randomInt (rngSeed : Nat) : Int :=
  let h := rngSeed * 1103515245 + 12345
  ((h / 65536) % 32768 : Nat) - 16384

/-- Generate a pseudo-random Point from a rngSeed -/
private def randomPoint (rngSeed : Nat) : Point :=
  { x := randomInt rngSeed, y := randomInt (rngSeed + 1) }

/-- Generate a pseudo-random Rectangle from a rngSeed -/
private def randomRectangle (rngSeed : Nat) : Rectangle :=
  { topLeft := randomPoint rngSeed, bottomRight := randomPoint (rngSeed + 2) }

/-! ## Property Test Functions -/

/--
Identity law: over t id s = s
-/
private def traversal_identity_prop (rngSeed : Nat) : Bool :=
  let xs : List Int := (List.range ((rngSeed % 10) + 1)).map (Int.ofNat ·)
  let tr : Traversal' (List Int) Int := Traversal.eachList
  (xs & tr %~ id) == xs

/--
Traversal preserves list length
-/
private def traversal_length_prop (rngSeed : Nat) : Bool :=
  let xs : List Int := (List.range ((rngSeed % 20) + 1)).map (Int.ofNat ·)
  let tr : Traversal' (List Int) Int := Traversal.eachList
  (xs & tr %~ (· + 1)).length == xs.length

/-! ## Effectful Traversals - Helper Types and Structures -/

-- Statistics accumulator for state test
private structure Stats where
  sum : Int
  count : Nat
  max : Int
deriving Repr, BEq

-- Diagnostic types for writer test
private inductive DiagLevel
  | info
  | warning
  | error
deriving Repr, BEq, Inhabited

private structure Diagnostic where
  level : DiagLevel
  message : String
deriving Repr, BEq, Inhabited

-- Validation type for error accumulation
private inductive Validation (ε α : Type _)
  | success : α → Validation ε α
  | failure : Array ε → Validation ε α
deriving Repr, BEq

private instance {ε : Type _} : Monad (Validation ε) where
  pure a := Validation.success a
  bind v f := match v with
    | Validation.success a => f a
    | Validation.failure errs => Validation.failure errs

private instance {ε : Type _} : Functor (Validation ε) where
  map f v := match v with
    | Validation.success a => Validation.success (f a)
    | Validation.failure errs => Validation.failure errs

private instance {ε : Type _} : Applicative (Validation ε) where
  pure a := Validation.success a
  seq vf va := match vf, va () with
    | Validation.success f, Validation.success a => Validation.success (f a)
    | Validation.success _, Validation.failure errs => Validation.failure errs
    | Validation.failure errs, Validation.success _ => Validation.failure errs
    | Validation.failure errs1, Validation.failure errs2 => Validation.failure (errs1 ++ errs2)

-- Form data for validation example
private structure FormData where
  name : String
  age : Int
  email : String
deriving Repr, BEq

-- Person data for polymorphism example
private structure Person where
  name : String
  age : Int
deriving Repr, BEq

-- Additional state structures for new tests
private structure NormState where
  sum : Int
  count : Nat
deriving Repr, BEq

private structure DedupState where
  prev : Option Int
  dupCount : Nat
deriving Repr, BEq

private structure MapState where
  nextId : Nat
  mapping : List (String × Nat)  -- Simple association list
deriving Repr, BEq

private structure FreqState where
  frequencies : List (Int × Nat)  -- (value, frequency)
deriving Repr, BEq

private structure WindowState where
  window : List Int
  maxSize : Nat
deriving Repr, BEq

private structure MeanState where
  sum : Int
  count : Nat
deriving Repr, BEq

/-! ## Traversal Laws Tests -/

test "Traversal Identity law: traverse id = id" := do
  let tr : Traversal' (List Int) Int := traversal List.walkMon
  let xs := [1, 2, 3]
  let result := xs & tr %~ (fun a => a)
  result ≡ xs

test "Tree traversal satisfies identity law" := do
  let tr : Traversal' (Tree Int) Int := traversal Tree.walkMon
  let tree := Tree.node (Tree.leaf 1) (Tree.leaf 2)
  let result := tree & tr %~ (fun a => a)
  result ≡ tree

test "Traversal over modifies all focuses" := do
  let tr : Traversal' (List Int) Int := traversal List.walkMon
  let xs := [1, 2, 3]
  let result := xs & tr %~ (· + 10)
  result ≡ [11, 12, 13]

test "Traverse with Option applicative short-circuits on none" := do
  let tr : Traversal' (List Int) Int := traversal List.walkMon
  let f : Int → Option Int := fun n => if n >= 0 then some (n + 1) else none

  let success := Traversal.traverse' tr f [0, 1, 2]
  success ≡ (some [1, 2, 3])

  let failure := Traversal.traverse' tr f [0, -1, 2]
  failure ≡ (none : Option (List Int))

test "Composed traversals satisfy identity law" := do
  let outer : Traversal' (List (Option Int)) (Option Int) := traversal List.walkMon
  let inner : Traversal' (Option Int) Int := traversal Option.walkMon
  let composed : Traversal' (List (Option Int)) Int := outer ∘ inner

  let xs := [some 1, none, some 3]
  let result := xs & composed %~ (fun a => a)
  result ≡ xs

test "Composed traversals modify all nested focuses" := do
  let outer : Traversal' (List (Option Int)) (Option Int) := traversal List.walkMon
  let inner : Traversal' (Option Int) Int := traversal Option.walkMon
  let composed : Traversal' (List (Option Int)) Int := outer ∘ inner

  let xs := [some 1, none, some 3]
  let result := xs & composed %~ (· * 2)
  result ≡ [some 2, none, some 6]

test "Tree traversal modifies all leaves" := do
  let tr : Traversal' (Tree Int) Int := traversal Tree.walkMon
  let tree := Tree.node (Tree.leaf 5) (Tree.node (Tree.leaf 10) (Tree.leaf 15))
  let result := tree & tr %~ (· + 1)
  let expected := Tree.node (Tree.leaf 6) (Tree.node (Tree.leaf 11) (Tree.leaf 16))
  result ≡ expected

test "Traversal law theorems can be invoked" := do
  let tr : Traversal' (List Int) Int := traversal List.walkMon

  -- Identity law: over tr id = id
  let test1 := [1, 2, 3] & tr %~ (fun a => a)
  test1 ≡ [1, 2, 3]

  -- Traverse with Id functor
  let test2 := Traversal.traverse' tr (F := Theorems.Id) (fun a => a + 5) [10, 20]
  test2 ≡ [15, 25]

test "Composition lawfulness instance is usable" := do
  -- Test via explicit composition instead of private composed_walk
  let outer : Traversal' (List (Option Int)) (Option Int) := traversal List.walkMon
  let inner : Traversal' (Option Int) Int := traversal Option.walkMon
  let composed : Traversal' (List (Option Int)) Int := outer ∘ inner

  -- Test identity
  let xs : List (Option Int) := [some 1, none, some 2]
  let result := xs & composed %~ (fun a => a)
  result ≡ xs

  -- Test modification
  let result2 := xs & composed %~ (· + 10)
  result2 ≡ [some 11, none, some 12]

test "Option traversal handles some and none correctly" := do
  let tr : Traversal' (Option Int) Int := traversal Option.walkMon

  -- Test with some
  let result1 := (some 4) & tr %~ (· * 3)
  result1 ≡ (some 12)

  -- Test with none
  let result2 := (none : Option Int) & tr %~ (· * 3)
  result2 ≡ none

  -- Test traverse with Option applicative
  let f : Int → Option Int := fun n => if n < 10 then some (n + 1) else none
  let success := Traversal.traverse' tr f (some 5)
  let failure := Traversal.traverse' tr f (some 15)
  success ≡ (some (some 6))
  failure ≡ (none : Option (Option Int))

test "Tree traversal with Option applicative validates all leaves" := do
  let tr : Traversal' (Tree Int) Int := traversal Tree.walkMon
  let tree := Tree.node (Tree.leaf 5) (Tree.leaf 3)

  let validate : Int → Option Int := fun n => if n > 0 then some n else none
  let result := Traversal.traverse' tr validate tree
  result ≡ (some tree)

  let badTree := Tree.node (Tree.leaf 5) (Tree.leaf (-1))
  let badResult := Traversal.traverse' tr validate badTree
  badResult ≡ (none : Option (Tree Int))

/-! ## Basic Traversal Tests -/

test "traversal over updates each list element" := do
  let tr : Traversal' (List Int) Int := Traversal.eachList
  let updated := [1, 2, 3] & tr %~ (· + 1)
  updated ≡ [2, 3, 4]

test "traversal traverse short-circuits via option applicative" := do
  let tr : Traversal' (List Int) Int := Traversal.eachList
  let step : Int → Option Int := fun n => if n ≥ 0 then some (n + 1) else none
  let success := Traversal.traverse' tr step [0, 2]
  let failure := Traversal.traverse' tr step [0, -1, 3]
  success ≡? [1, 3]
  shouldBeNone failure

test "fold toList collects focuses in order" := do
  let fld : Fold' (Option Int) Int :=
    Fold.ofAffine (s := Option Int) (t := Option Int) (a := Int) (b := Int)
      (AffineTraversalOps.ofPrism optionPrism)
  Fold.toList fld (some 7) ≡ [7]
  Fold.toList fld none ≡ ([] : List Int)

test "fold foldMap aggregates via monoid" := do
  let fld : Fold' Point Int := Fold.ofLens pointLens
  let points := [{ x := 2, y := 1 }, { x := -1, y := 5 }, { x := 4, y := 9 }]
  let lifted := points.map (Fold.toList fld)
  lifted ≡ ([[2], [-1], [4]] : List (List Int))

test "fold length counts focuses" := do
  let fld : Fold' Point Int := Fold.ofLens pointLens
  (Fold.toList fld { x := 5, y := 0 }).length ≡ 1

test "setter set updates value" := do
  let st : Lens' Point Int := pointLens
  let updated := { x := 1, y := 2 } & st .~ 42
  updated ≡ { x := 42, y := 2 }

test "affine traversal preview and set behaves correctly" := do
  let affine : AffineTraversal' (Option Int) Int :=
    AffineTraversalOps.ofPrism optionPrism
  (some 5) ^? affine ≡? 5
  shouldBeNone (none ^? affine)
  let reset := (some 1) & affine .~ 99
  reset ≡ some 99

/-! ## Effectful Traversals Tests -/

test "Option applicative: validate all positive (short-circuit)" := do
    -- Validation function: accept only positive numbers
    let validatePositive : Int → Option Int :=
      fun n => if n > 0 then some n else none

    -- Test 1: All positive - succeeds
    let allPositive : List Int := [1, 2, 3, 4, 5]
    let result1 := Traversal.traverse' traversed validatePositive allPositive
    result1 ≡ (some [1, 2, 3, 4, 5])

    -- Test 2: Contains negative - short-circuits to None
    let hasNegative : List Int := [1, 2, -3, 4, 5]
    let result2 := Traversal.traverse' traversed validatePositive hasNegative
    result2 ≡ (none : Option (List Int))

    -- Test 3: First element negative - immediate failure
    let firstNegative : List Int := [-1, 2, 3]
    let result3 := Traversal.traverse' traversed validatePositive firstNegative
    result3 ≡ (none : Option (List Int))

    -- Test 4: Empty list - succeeds trivially
    let empty : List Int := []
    let result4 := Traversal.traverse' traversed validatePositive empty
    result4 ≡ (some [])

    -- Test 5: Zero is not positive - should fail
    let hasZero : List Int := [1, 0, 3]
    let result5 := Traversal.traverse' traversed validatePositive hasZero
    result5 ≡ (none : Option (List Int))

test "Option applicative: safe division (short-circuit on zero)" := do
    -- Safe division function: returns None if divisor is zero
    let safeDivide (divisor : Int) (dividend : Int) : Option Int :=
      if divisor = 0 then none else some (dividend / divisor)

    -- Test 1: All non-zero divisors - succeeds
    let divisors : List Int := [2, 4, 5, 10]
    let dividend := 100
    let result1 := Traversal.traverse' traversed (safeDivide · dividend) divisors
    result1 ≡ (some [50, 25, 20, 10])

    -- Test 2: Contains zero - short-circuits to None
    let hasZero : List Int := [2, 4, 0, 10]
    let result2 := Traversal.traverse' traversed (safeDivide · dividend) hasZero
    result2 ≡ (none : Option (List Int))

    -- Test 3: First element zero - immediate failure
    let firstZero : List Int := [0, 2, 4]
    let result3 := Traversal.traverse' traversed (safeDivide · dividend) firstZero
    result3 ≡ (none : Option (List Int))

    -- Test 4: Last element zero - processes all then fails
    let lastZero : List Int := [2, 4, 5, 0]
    let result4 := Traversal.traverse' traversed (safeDivide · dividend) lastZero
    result4 ≡ (none : Option (List Int))

    -- Test 5: Empty list - succeeds trivially
    let empty : List Int := []
    let result5 := Traversal.traverse' traversed (safeDivide · dividend) empty
    result5 ≡ (some [])

    -- Test 6: Negative divisors are fine
    let negatives : List Int := [-2, -5, 10]
    let result6 := Traversal.traverse' traversed (safeDivide · dividend) negatives
    result6 ≡ (some [-50, -20, 10])


test "State applicative: number elements sequentially" := do
    -- Stateful function: pair each element with current counter, then increment
    let numberElement (x : String) : StateT Nat _root_.Id (Nat × String) := do
      let n ← get
      set (n + 1)
      pure (n, x)

    -- Test 1: Number elements starting from 0
    let fruits := ["apple", "banana", "cherry"]
    let (result1, finalCount1) := (Traversal.traverse' traversed numberElement fruits).run 0
    result1 ≡ [(0, "apple"), (1, "banana"), (2, "cherry")]
    finalCount1 ≡ 3

    -- Test 2: Number elements starting from 10
    let colors := ["red", "green", "blue"]
    let (result2, finalCount2) := (Traversal.traverse' traversed numberElement colors).run 10
    result2 ≡ [(10, "red"), (11, "green"), (12, "blue")]
    finalCount2 ≡ 13

    -- Test 3: Empty list - counter unchanged
    let empty : List String := []
    let (result3, finalCount3) := (Traversal.traverse' traversed numberElement empty).run 5
    result3 ≡ []
    finalCount3 ≡ 5

    -- Test 4: Single element
    let single := ["only"]
    let (result4, finalCount4) := (Traversal.traverse' traversed numberElement single).run 99
    result4 ≡ [(99, "only")]
    finalCount4 ≡ 100

    -- Test 5: Demonstrate state threading - use counter to create indices
    let addIndex (x : Int) : StateT Nat _root_.Id String := do
      let idx ← get
      set (idx + 1)
      pure s!"[{idx}]={x}"

    let numbers := [10, 20, 30]
    let (indexed, _) := (Traversal.traverse' traversed addIndex numbers).run 1
    indexed ≡ ["[1]=10", "[2]=20", "[3]=30"]

test "State applicative: accumulate statistics with transformations" := do
    -- Stateful function: double each number and accumulate statistics
    let doubleAndAccumulate (x : Int) : StateT Stats _root_.Id Int := do
      let stats ← get
      set ({
        sum := stats.sum + x,
        count := stats.count + 1,
        max := max stats.max x
      } : Stats)
      pure (x * 2)

    -- Test 1: Accumulate sum, count, and max while doubling
    let numbers := [5, 2, 8, 1, 9]
    let initialStats : Stats := { sum := 0, count := 0, max := 0 }
    let (doubled, finalStats) := (Traversal.traverse' traversed doubleAndAccumulate numbers).run initialStats
    doubled ≡ [10, 4, 16, 2, 18]
    finalStats.sum ≡ 25
    finalStats.count ≡ 5
    finalStats.max ≡ 9

    -- Test 2: Transform with running average calculation
    let accumulateForAvg (x : Int) : StateT (Int × Nat) _root_.Id Int := do
      let (sum, count) ← get
      let newSum := sum + x
      let newCount := count + 1
      set (newSum, newCount)
      pure (x + 10)  -- Transform: add 10 to each element

    let values := [15, 25, 35]
    let result2 := (Traversal.traverse' traversed accumulateForAvg values).run (0, 0)
    result2.1 ≡ [25, 35, 45]
    result2.2.1 ≡ 75
    result2.2.2 ≡ 3
    -- Average would be: totalSum / totalCount = 75 / 3 = 25

    -- Test 3: Empty list - stats unchanged
    let empty : List Int := []
    let (emptyResult, emptyStats) := (Traversal.traverse' traversed doubleAndAccumulate empty).run initialStats
    emptyResult ≡ []
    emptyStats ≡ initialStats

    -- Test 4: Single element accumulation
    let single := [42]
    let (singleResult, singleStats) := (Traversal.traverse' traversed doubleAndAccumulate single).run initialStats
    singleResult ≡ [84]
    singleStats.sum ≡ 42
    singleStats.count ≡ 1
    singleStats.max ≡ 42


test "Writer applicative: log each transformation step" := do
    -- Transformation function that logs before/after for each element
    let transformAndLog (x : Int) : WriterT (Array String) _root_.Id Int := do
      let result := x * 2 + 1
      tell #[s!"Transform {x} -> {result}"]
      pure result

    -- Test 1: Log all transformations
    let numbers := [3, 5, 7]
    let (transformed, log) := (Traversal.traverse' traversed transformAndLog numbers).run
    transformed ≡ [7, 11, 15]
    log ≡ #["Transform 3 -> 7", "Transform 5 -> 11", "Transform 7 -> 15"]

    -- Test 2: Empty list produces empty log
    let empty : List Int := []
    let (emptyResult, emptyLog) := (Traversal.traverse' traversed transformAndLog empty).run
    emptyResult ≡ []
    emptyLog ≡ #[]

    -- Test 3: Single element
    let single := [10]
    let (singleResult, singleLog) := (Traversal.traverse' traversed transformAndLog single).run
    singleResult ≡ [21]
    singleLog ≡ #["Transform 10 -> 21"]

    -- Test 4: Log validation messages during transformation
    let validateAndTransform (x : Int) : WriterT (Array String) _root_.Id Int := do
      if x < 0 then
        tell #[s!"Warning: negative value {x}"]
      else if x = 0 then
        tell #[s!"Warning: zero value"]
      else
        tell #[s!"OK: {x}"]
      pure (x.natAbs)

    let mixed := [-5, 0, 10, -2]
    let result4 := (Traversal.traverse' traversed validateAndTransform mixed).run
    result4.1 ≡ [5, 0, 10, 2]
    result4.2 ≡ #["Warning: negative value -5", "Warning: zero value", "OK: 10", "Warning: negative value -2"]

    -- Test 5: Accumulate computations with details
    let computeWithDetail (x : Int) : WriterT (Array String) _root_.Id Int := do
      let squared := x * x
      let doubled := squared * 2
      tell #[s!"{x}² = {squared}, then *2 = {doubled}"]
      pure doubled

    let inputs := [2, 3]
    let result5 := (Traversal.traverse' traversed computeWithDetail inputs).run
    result5.1 ≡ [8, 18]
    result5.2 ≡ #["2² = 4, then *2 = 8", "3² = 9, then *2 = 18"]


test "Writer applicative: collect diagnostics during traversal" := do
    -- Transformation with diagnostic collection
    let processWithDiagnostics (x : Int) : WriterT (Array Diagnostic) _root_.Id Int := do
      if x < 0 then
        tell #[{ level := DiagLevel.error, message := s!"Negative value: {x}" }]
        pure 0
      else if x = 0 then
        tell #[{ level := DiagLevel.warning, message := "Zero value encountered" }]
        pure 0
      else if x > 100 then
        tell #[{ level := DiagLevel.warning, message := s!"Large value: {x}" }]
        pure x
      else
        tell #[{ level := DiagLevel.info, message := s!"Processing: {x}" }]
        pure x

    -- Test 1: Collect mixed diagnostics
    let values := [50, -10, 0, 150, 25]
    let result := (Traversal.traverse' traversed processWithDiagnostics values).run
    result.1 ≡ [50, 0, 0, 150, 25]
    result.2.size ≡ 5
    result.2[0]! ≡ { level := DiagLevel.info, message := "Processing: 50" }
    result.2[1]! ≡ { level := DiagLevel.error, message := "Negative value: -10" }
    result.2[2]! ≡ { level := DiagLevel.warning, message := "Zero value encountered" }

    -- Test 2: Multiple diagnostics per element
    let processWithMultipleDiagnostics (x : Int) : WriterT (Array Diagnostic) _root_.Id Int := do
      tell #[{ level := DiagLevel.info, message := s!"Starting process: {x}" }]
      let result := x * 2
      if result > 50 then
        tell #[{ level := DiagLevel.warning, message := s!"Result {result} exceeds threshold" }]
      tell #[{ level := DiagLevel.info, message := s!"Completed: {x} -> {result}" }]
      pure result

    let inputs := [10, 30]
    let result2 := (Traversal.traverse' traversed processWithMultipleDiagnostics inputs).run
    result2.1 ≡ [20, 60]
    result2.2.size ≡ 5
    -- 10: start, complete (2)
    -- 30: start, warning, complete (3)

    -- Test 3: Filter diagnostics by level (post-processing)
    let countByLevel (diags : Array Diagnostic) (level : DiagLevel) : Nat :=
      diags.foldl (fun acc d => if d.level == level then acc + 1 else acc) 0

    let testValues := [5, -1, 200, 0, 10]
    let result3 := (Traversal.traverse' traversed processWithDiagnostics testValues).run
    let errorCount := countByLevel result3.2 DiagLevel.error
    let warningCount := countByLevel result3.2 DiagLevel.warning
    let infoCount := countByLevel result3.2 DiagLevel.info
    errorCount ≡ 1
    warningCount ≡ 2
    infoCount ≡ 2

    -- Test 4: Empty list produces no diagnostics
    let empty : List Int := []
    let result4 := (Traversal.traverse' traversed processWithDiagnostics empty).run
    result4.1 ≡ []
    result4.2.size ≡ 0


test "Validation applicative: accumulate all errors (vs Option short-circuit)" := do
    -- Validation function that returns error for invalid values
    let validatePositive (x : Int) : Validation String Int :=
      if x > 0 then
        Validation.success x
      else
        Validation.failure #[s!"Value {x} is not positive"]

    -- Test 1: All valid - succeeds
    let allValid := [1, 2, 3, 4]
    let result1 := Traversal.traverse' traversed validatePositive allValid
    match result1 with
    | Validation.success vals =>
      vals ≡ [1, 2, 3, 4]
    | Validation.failure _ =>
      IO.throwServerError "Expected success but got failure"

    -- Test 2: Multiple failures - ACCUMULATES ALL (not short-circuit like Option)
    let multipleInvalid := [1, -2, 3, -4, 0]
    let result2 := Traversal.traverse' traversed validatePositive multipleInvalid
    match result2 with
    | Validation.success _ =>
      IO.throwServerError "Expected failure but got success"
    | Validation.failure errs =>
      errs.size ≡ 3
      errs[0]! ≡ "Value -2 is not positive"
      errs[1]! ≡ "Value -4 is not positive"
      errs[2]! ≡ "Value 0 is not positive"

    -- Test 3: Compare with Option (short-circuits on first error)
    let optionValidate (x : Int) : Option Int :=
      if x > 0 then some x else none

    let result3Option := Traversal.traverse' traversed optionValidate multipleInvalid
    match result3Option with
    | none => pure ()  -- Option just returns None, doesn't tell us which/how many failed
    | some _ => IO.throwServerError "Expected None"

    -- Key insight: Validation gives us ALL errors, Option gives us nothing
    let result3Validation := Traversal.traverse' traversed validatePositive multipleInvalid
    match result3Validation with
    | Validation.failure errs =>
      errs.size ≡ 3
    | Validation.success _ =>
      IO.throwServerError "Expected failure"

    -- Test 4: Form validation use case - validate multiple fields
    let validateField (field : String) (condition : Bool) : Validation String Unit :=
      if condition then
        Validation.success ()
      else
        Validation.failure #[s!"{field} is invalid"]

    let validateForm (form : FormData) : Validation String FormData :=
      -- Validate all fields and accumulate errors
      let nameValid := validateField "name" (!form.name.isEmpty)
      let ageValid := validateField "age" (form.age >= 0 && form.age <= 150)
      let emailValid := validateField "email" (form.email.contains '@')

      match nameValid, ageValid, emailValid with
      | Validation.success _, Validation.success _, Validation.success _ =>
        Validation.success form
      | _, _, _ =>
        let errors := #[]
        let errors := match nameValid with
          | Validation.failure e => errors ++ e
          | _ => errors
        let errors := match ageValid with
          | Validation.failure e => errors ++ e
          | _ => errors
        let errors := match emailValid with
          | Validation.failure e => errors ++ e
          | _ => errors
        Validation.failure errors

    let badForm : FormData := { name := "", age := -5, email := "notanemail" }
    match validateForm badForm with
    | Validation.failure errs =>
      errs.size ≡ 3
    | Validation.success _ =>
      IO.throwServerError "Expected validation failure"

    -- Test 5: Empty list succeeds trivially
    let empty : List Int := []
    let result5 := Traversal.traverse' traversed validatePositive empty
    match result5 with
    | Validation.success vals =>
      vals ≡ []
    | Validation.failure _ =>
      IO.throwServerError "Empty list should succeed"


test "State applicative: replace elements with running sum" := do
    -- Stateful function: replace each element with current sum, then add element to sum
    let replaceWithSum (x : Int) : StateT Int _root_.Id Int := do
      let currentSum ← get
      set (currentSum + x)
      pure currentSum  -- Return sum BEFORE adding current element

    -- Test 1: Running sum starting from 0
    let numbers := [5, 10, 15, 20]
    let (result1, finalSum1) := (Traversal.traverse' traversed replaceWithSum numbers).run 0
    result1 ≡ [0, 5, 15, 30]
    finalSum1 ≡ 50

    -- Test 2: Running sum starting from 100
    let (result2, finalSum2) := (Traversal.traverse' traversed replaceWithSum numbers).run 100
    result2 ≡ [100, 105, 115, 130]
    finalSum2 ≡ 150

    -- Test 3: Empty list - sum unchanged
    let empty : List Int := []
    let (result3, finalSum3) := (Traversal.traverse' traversed replaceWithSum empty).run 42
    result3 ≡ []
    finalSum3 ≡ 42

    -- Test 4: Negative numbers
    let mixed := [10, -5, 20, -15]
    let (result4, finalSum4) := (Traversal.traverse' traversed replaceWithSum mixed).run 0
    result4 ≡ [0, 10, 5, 25]
    finalSum4 ≡ 10

    -- Test 5: Replace with running product
    let replaceWithProduct (x : Int) : StateT Int _root_.Id Int := do
      let currentProduct ← get
      set (currentProduct * x)
      pure currentProduct

    let factors := [2, 3, 4]
    let result5 := (Traversal.traverse' traversed replaceWithProduct factors).run 1
    result5.1 ≡ [1, 2, 6]
    result5.2 ≡ 24


test "State applicative: normalize values by running mean" := do
    -- Normalize by running mean: transform each value, then update statistics
    let normalizeByMean (x : Int) : StateT NormState _root_.Id Int := do
      let state ← get
      let currentMean := if state.count > 0 then state.sum / state.count else 0
      set ({ sum := state.sum + x, count := state.count + 1 } : NormState)
      pure (x - currentMean)  -- Subtract current mean from value

    -- Test 1: Normalize sequence
    let values := [10, 20, 30, 40]
    let initialState : NormState := { sum := 0, count := 0 }
    let result := (Traversal.traverse' traversed normalizeByMean values).run initialState
    result.1 ≡ [10, 10, 15, 20]
    -- [10-0, 20-10, 30-15, 40-20]
    result.2.sum ≡ 100
    result.2.count ≡ 4

    -- Test 2: Scale by running max
    let scaleByMax (x : Int) : StateT Int _root_.Id Int := do
      let currentMax ← get
      let newMax := max currentMax x
      set newMax
      if currentMax > 0 then
        pure (x * 100 / currentMax)  -- Scale as percentage of current max
      else
        pure 100  -- First element is 100%

    let sequence := [50, 100, 75, 200]
    let result2 := (Traversal.traverse' traversed scaleByMax sequence).run 0
    result2.1 ≡ [100, 200, 75, 200]
    -- [100% (first), 100*100/50=200%, 75*100/100=75%, 200*100/100=200%]


test "State applicative: mark duplicates of previous element" := do
    -- State tracks the previous element
    -- Replace duplicates with a marker value
    let dedup (marker : Int) (x : Int) : StateT (Option Int) _root_.Id Int := do
      let prev ← get
      set (some x)
      match prev with
      | none => pure x  -- First element, keep it
      | some p => if p == x then pure marker else pure x

    -- Test 1: Deduplicate consecutive duplicates
    let withDups := [1, 1, 2, 2, 2, 3, 1, 1]
    let (result1, _) := (Traversal.traverse' traversed (dedup (-1)) withDups).run none
    result1 ≡ [1, -1, 2, -1, -1, 3, 1, -1]

    -- Test 2: No duplicates
    let noDups := [1, 2, 3, 4, 5]
    let (result2, _) := (Traversal.traverse' traversed (dedup (-1)) noDups).run none
    result2 ≡ [1, 2, 3, 4, 5]

    -- Test 3: All same
    let allSame := [7, 7, 7, 7]
    let (result3, _) := (Traversal.traverse' traversed (dedup 0) allSame).run none
    result3 ≡ [7, 0, 0, 0]

    -- Test 4: Empty list
    let empty : List Int := []
    let (result4, _) := (Traversal.traverse' traversed (dedup (-1)) empty).run none
    result4 ≡ []

    -- Test 5: Count consecutive duplicates
    let countDuplicates (x : Int) : StateT DedupState _root_.Id Int := do
      let state ← get
      match state.prev with
      | none =>
        set ({ prev := some x, dupCount := 0 } : DedupState)
        pure x
      | some p =>
        if p == x then
          set ({ prev := some x, dupCount := state.dupCount + 1 } : DedupState)
          pure x
        else
          set ({ prev := some x, dupCount := state.dupCount } : DedupState)
          pure x

    let testSeq := [5, 5, 5, 3, 3, 1]
    let result5 := (Traversal.traverse' traversed countDuplicates testSeq).run
      { prev := none, dupCount := 0 }
    result5.2.dupCount ≡ 3


test "State applicative: build replacement map during traversal" := do
    -- Build a replacement map as we traverse: first occurrence gets ID, repeats use that ID
    let assignId (s : String) : StateT MapState _root_.Id Nat := do
      let state ← get
      -- Look up if we've seen this string before
      match state.mapping.find? (fun pair => pair.1 == s) with
      | some pair => pure pair.2  -- Return existing ID
      | none =>
        let newId := state.nextId
        set ({
          nextId := state.nextId + 1,
          mapping := (s, newId) :: state.mapping
        } : MapState)
        pure newId

    -- Test 1: Assign unique IDs to strings, reuse for duplicates
    let words := ["apple", "banana", "apple", "cherry", "banana", "apple"]
    let initialState : MapState := { nextId := 0, mapping := [] }
    let result := (Traversal.traverse' traversed assignId words).run initialState
    result.1 ≡ [0, 1, 0, 2, 1, 0]
    result.2.nextId ≡ 3
    result.2.mapping.length ≡ 3

    -- Test 2: Empty list
    let empty : List String := []
    let result2 := (Traversal.traverse' traversed assignId empty).run initialState
    result2.1 ≡ []
    result2.2.nextId ≡ 0

    -- Test 3: All unique
    let unique := ["a", "b", "c", "d"]
    let result3 := (Traversal.traverse' traversed assignId unique).run initialState
    result3.1 ≡ [0, 1, 2, 3]
    result3.2.nextId ≡ 4

    -- Test 4: Replace based on accumulated frequency
    let replaceByFrequency (x : Int) : StateT FreqState _root_.Id Nat := do
      let state ← get
      match state.frequencies.find? (fun pair => pair.1 == x) with
      | some pair =>
        -- Update frequency
        let freq := pair.2
        let newFreqs := state.frequencies.map fun (v, f) =>
          if v == x then (v, f + 1) else (v, f)
        set ({ frequencies := newFreqs } : FreqState)
        pure (freq + 1)  -- Return new frequency
      | none =>
        set ({ frequencies := (x, 1) :: state.frequencies } : FreqState)
        pure 1  -- First occurrence

    let numbers := [5, 3, 5, 5, 3, 7, 5]
    let result4 := (Traversal.traverse' traversed replaceByFrequency numbers).run
      { frequencies := [] }
    result4.1 ≡ [1, 1, 2, 3, 2, 1, 4]
    -- 5 appears: 1st, 2nd, 3rd, 4th time
    -- 3 appears: 1st, 2nd time
    -- 7 appears: 1st time


test "State applicative: sliding window transformations" := do
    -- Replace each element with average of current window
    let windowAverage (x : Int) : StateT WindowState _root_.Id Int := do
      let state ← get
      let newWindow := (x :: state.window).take state.maxSize
      set ({ window := newWindow, maxSize := state.maxSize } : WindowState)
      let sum := newWindow.foldl (· + ·) 0
      let count := newWindow.length
      pure (if count > 0 then sum / count else 0)

    -- Test 1: Window size 2 - average of current and previous
    let numbers := [10, 20, 30, 40, 50]
    let initialState : WindowState := { window := [], maxSize := 2 }
    let (averages, _) := (Traversal.traverse' traversed windowAverage numbers).run initialState
    averages ≡ [10, 15, 25, 35, 45]
    -- [10/1, (20+10)/2, (30+20)/2, (40+30)/2, (50+40)/2]

    -- Test 2: Window size 3
    let (averages3, _) := (Traversal.traverse' traversed windowAverage numbers).run
      { window := [], maxSize := 3 }
    averages3 ≡ [10, 15, 20, 30, 40]
    -- [10/1, (20+10)/2, (30+20+10)/3, (40+30+20)/3, (50+40+30)/3]

    -- Test 3: Window size 1 (no averaging)
    let (averages1, _) := (Traversal.traverse' traversed windowAverage numbers).run
      { window := [], maxSize := 1 }
    averages1 ≡ [10, 20, 30, 40, 50]

    -- Test 4: Compute differences from previous element
    let computeDelta (x : Int) : StateT (Option Int) _root_.Id Int := do
      let prev ← get
      set (some x)
      match prev with
      | none => pure 0  -- First element: no previous
      | some p => pure (x - p)

    let sequence := [5, 8, 6, 9, 12]
    let result4 := (Traversal.traverse' traversed computeDelta sequence).run none
    result4.1 ≡ [0, 3, -2, 3, 3]

    -- Test 5: Running differences (element minus running mean)
    let deltaFromMean (x : Int) : StateT MeanState _root_.Id Int := do
      let state ← get
      let mean := if state.count > 0 then state.sum / state.count else x
      set ({ sum := state.sum + x, count := state.count + 1 } : MeanState)
      pure (x - mean)

    let values := [100, 200, 150, 250]
    let result5 := (Traversal.traverse' traversed deltaFromMean values).run
      { sum := 0, count := 0 }
    result5.1 ≡ [0, 100, 0, 100]
    -- [100-100, 200-100, 150-150, 250-150]

test "Polymorphism: same traversal, multiple effect types" := do
    -- Define a single list to traverse
    let numbers : List Int := [5, 10, 15, 20]

    -- Define a processing function that can be used with ANY applicative
    -- The type signature is polymorphic over the effect type F
    let processNumber (threshold : Int) (x : Int) {F : Type → Type} [Applicative F]
        (successFn : Int → F Int) (failFn : String → F Int) : F Int :=
      if x >= threshold then
        successFn x
      else
        failFn s!"Value {x} below threshold {threshold}"

    -- Use case 1: Option - fail-fast validation
    let optionProcess := processNumber 5  -- threshold of 5, all values pass
    let optionResult := Traversal.traverse' traversed
      (fun x => optionProcess x (fun v => some v) (fun _ => none))
      numbers
    match optionResult with
    | some vals =>
      vals ≡ [5, 10, 15, 20]
    | none =>
      IO.throwServerError "Should not fail"

    let failNumbers := [5, 3, 15]
    let optionResult2 := Traversal.traverse' traversed
      (fun x => optionProcess x (fun v => some v) (fun _ => none))
      failNumbers
    match optionResult2 with
    | none =>
      pure ()  -- Expected: fails fast on first value < 10
    | some _ =>
      IO.throwServerError "Should fail"

    -- Use case 2: State - count how many values meet threshold
    let stateFn (x : Int) : StateT Nat _root_.Id Int :=
      if x >= 10 then do
        modify (· + 1)
        pure x
      else
        pure x
    let stateResult := (Traversal.traverse' traversed stateFn numbers).run 0
    stateResult.1 ≡ [5, 10, 15, 20]
    stateResult.2 ≡ 3

    -- Use case 3: Writer - log which values are processed
    let writerFn (x : Int) : WriterT (Array String) _root_.Id Int := do
      if x >= 10 then
        tell #[s!"Accepted: {x}"]
      else
        tell #[s!"Below threshold: {x}"]
      pure x
    let writerResult := (Traversal.traverse' traversed writerFn numbers).run
    writerResult.1 ≡ [5, 10, 15, 20]
    writerResult.2.size ≡ 4
    writerResult.2[0]! ≡ "Below threshold: 5"
    writerResult.2[1]! ≡ "Accepted: 10"

    -- Use case 4: Validation - collect ALL failures (not fail-fast)
    let validationFn (x : Int) : Validation String Int :=
      if x >= 10 then
        Validation.success x
      else
        Validation.failure #[s!"Value {x} is below threshold 10"]
    let validationResult := Traversal.traverse' traversed validationFn failNumbers
    match validationResult with
    | Validation.failure errs =>
      errs.size ≡ 2
      errs[0]! ≡ "Value 5 is below threshold 10"
      errs[1]! ≡ "Value 3 is below threshold 10"
    | Validation.success _ =>
      IO.throwServerError "Should accumulate errors"

    -- Key insight demonstration: The traversal is the SAME (`Traversal.traverse' traversed`)
    -- Only the effectful function changes!
    -- - Option: fail-fast, returns Some or None
    -- - State: thread state through traversal
    -- - Writer: collect logs during traversal
    -- - Validation: accumulate all errors

    -- Use case 5: Demonstrate with a more complex traversal
    let people : List Person := [
      { name := "Alice", age := 25 },
      { name := "Bob", age := 17 },
      { name := "Charlie", age := 30 }
    ]

    -- Same traversal, different effects!

    -- With Option: validate all are adults
    let optionValidate (p : Person) : Option Person :=
      if p.age >= 18 then some p else none
    let optionPeople := Traversal.traverse' traversed optionValidate people
    match optionPeople with
    | none => pure ()  -- Bob is 17, fails
    | some _ => IO.throwServerError "Should fail on Bob"

    -- With Writer: log age checks
    let writerValidate (p : Person) : WriterT (Array String) _root_.Id Person := do
      if p.age >= 18 then
        tell #[s!"{p.name} (age {p.age}): adult"]
      else
        tell #[s!"{p.name} (age {p.age}): minor"]
      pure p
    let peopleWriterResult := (Traversal.traverse' traversed writerValidate people).run
    peopleWriterResult.2.size ≡ 3
    peopleWriterResult.2[0]! ≡ "Alice (age 25): adult"
    peopleWriterResult.2[1]! ≡ "Bob (age 17): minor"

    -- With Validation: collect all minors
    let validationValidate (p : Person) : Validation String Person :=
      if p.age >= 18 then
        Validation.success p
      else
        Validation.failure #[s!"{p.name} is {p.age} years old (under 18)"]
    let validationPeople := Traversal.traverse' traversed validationValidate people
    match validationPeople with
    | Validation.failure errs =>
      errs.size ≡ 1
      errs[0]! ≡ "Bob is 17 years old (under 18)"
    | Validation.success _ =>
      IO.throwServerError "Should report minor"

/-! ## Property-Based Tests -/

test "Property: Traversal identity law (100 samples)" := do
  for i in [:100] do
    ensure (traversal_identity_prop i) s!"Identity failed for seed {i}"

test "Property: Traversal preserves length (100 samples)" := do
  for i in [:100] do
    ensure (traversal_length_prop i) s!"Length failed for seed {i}"

test "Stress: Large list (1000 elements) traversal" := do
  let largeList : List Int := (List.range 1000).map (Int.ofNat ·)
  let tr : Traversal' (List Int) Int := Traversal.eachList
  let result := largeList & tr %~ (· + 1)
  result.length ≡ 1000
  result.head? ≡? 1

end CollimatorTests.TraversalTests
