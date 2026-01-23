import Batteries
import Collimator.Combinators
import Collimator.Operators
import Collimator.Instances
import Collimator.Optics
import Collimator.Concrete.FunArrow
import Collimator.Prelude
import Collimator.Helpers
import Crucible

/-!
# Consolidated Combinator Tests

This file consolidates tests from:
- CollimatorTests/Combinators.lean
- CollimatorTests/NewCombinators.lean
- CollimatorTests/AdvancedShowcase/FilteredIndexed.lean
- CollimatorTests/AdvancedFeatures.lean

Tests cover:
- Product/sum instances
- List operations (ix, at, head, last, taking, dropping)
- Filtered and indexed traversals
- String optics
- Bifunctor traversals
- Plated typeclass
- Operator syntax
-/

namespace CollimatorTests.CombinatorTests

open Batteries
open Collimator
open Collimator.Combinators
open Collimator.Indexed
open Collimator.Operators
open Collimator.Instances.List
open Collimator.Instances.Option
open Collimator.Instances.String
open Collimator.Combinators.Bitraversal
open Collimator.Combinators
open Crucible

open scoped Collimator.Operators

testSuite "Combinator Tests"

/-! ## Basic Operator and Instance Tests -/

structure Player where
  name : String
  score : Int
  deriving BEq, Repr

private def scoreLens : Lens' Player Int :=
  lens' (fun p => p.score) (fun p s => { p with score := s })

test "operator syntax view/over/set works for lenses" := do
  let p : Player := { name := "Ada", score := 10 }
  (p ^. scoreLens) ≡ 10
  let updated := p & scoreLens %~ (· + 5)
  (updated ^. scoreLens) ≡ 15
  let reset := p & scoreLens .~ 0
  (reset ^. scoreLens) ≡ 0

test "product instances supply convenient lenses" := do
  let pair := (3, true)
  let firstLens : Lens' (Int × Bool) Int :=
    Collimator.Instances.Prod.first (α := Int) (β := Bool) (γ := Int)
  let secondLens : Lens' (Int × Bool) Bool :=
    Collimator.Instances.Prod.second (α := Int) (β := Bool) (γ := Bool)
  let bumpedFirst := pair & firstLens %~ (· + 1)
  bumpedFirst ≡ (4, true)
  let toggled := pair & secondLens %~ not
  toggled ≡ (3, false)
  let triple : (Int × Int) × Int := ((1, 2), 3)
  let lens : Lens' ((Int × Int) × Int) Int :=
    Collimator.Instances.Prod.firstOfTriple (α := Int) (β := Int) (γ := Int) (δ := Int)
  let incremented := triple & lens %~ (· + 10)
  incremented ≡ ((11, 2), 3)

test "sum prisms preview and review branches" := do
  let leftPrism : Prism (Sum Int String) (Sum Int String) Int Int :=
    Collimator.Instances.Sum.left
      (α := Int) (β := String) (γ := Int)
  let inLeft : Sum Int String := Sum.inl (7 : Int)
  let inRight : Sum Int String := Sum.inr (α := Int) ("optics" : String)
  (inLeft ^? leftPrism) ≡ (some (7 : Int))
  (inRight ^? leftPrism) ≡ (none : Option Int)
  let expectedReview : Sum Int String := Sum.inl (5 : Int)
  (review' leftPrism (5 : Int)) ≡ expectedReview

test "option prisms distinguish some and none" := do
  let somePrism : Prism (Option Int) (Option Int) Int Int :=
    Collimator.Instances.Option.somePrism (α := Int) (β := Int)
  ((some 9) ^? somePrism) ≡ (some 9)
  (none ^? somePrism) ≡ (none : Option Int)
  (review' somePrism 4) ≡ (some 4)

test "list ix updates element at index" := do
  let elements := [10, 20, 30]
  let traversal : Traversal' (List Int) Int :=
    ix (ι := Nat) (s := List Int) (a := Int) 1
  let updated := elements & traversal %~ (· + 7)
  updated ≡ [10, 27, 30]

test "list at lens views optional element" := do
  let xs := ["lean", "optic", "library"]
  let l : Lens' (List String) (Option String) :=
    atLens (ι := Nat) (s := List String) (a := String) 2
  (xs ^. l) ≡ (some "library")
  (["lean"] ^. l) ≡ (none : Option String)

test "array ix modifies in-bounds value and ignores out-of-bounds" := do
  let arr : Array Int := #[1, 2, 3]
  let traversal : Traversal' (Array Int) Int :=
    ix (ι := Nat) (s := Array Int) (a := Int) 0
  let updated := arr & traversal %~ (· * 2)
  updated ≡ #[2, 2, 3]
  let untouched := arr & (ix (ι := Nat) (s := Array Int) (a := Int) 5) %~ (· + 1)
  untouched ≡ #[1, 2, 3]

test "filtered traversal only updates predicate matches" := do
  let tr : Traversal' (List Int) Int :=
    Collimator.Instances.List.traversed (α := Int) (β := Int)
  let evens : Traversal' (List Int) Int :=
    filtered tr (fun n => n % 2 == 0)
  let result := [1, 2, 3, 4] & evens %~ (· + 1)
  result ≡ [1, 3, 3, 5]

test "itraversed exposes index during updates" := do
  let base : Traversal' (List Int) (Nat × Int) :=
    Collimator.Instances.List.itraversed
  let bumped := [5, 5, 5] & base %~ (fun | (idx, v) => (idx, v + idx))
  bumped ≡ [5, 6, 7]

/-! ## filteredList and ifilteredList Tests -/

test "filteredList: double only positive numbers" := do
  let result := [-1, 2, -3, 4] & filteredList (· > 0) %~ (· * 2)
  result ≡ [-1, 4, -3, 8]

test "filteredList: filter none" := do
  let result := [1, 2, 3] & filteredList (· > 100) %~ (· * 2)
  result ≡ [1, 2, 3]

test "filteredList: filter all" := do
  let result := [1, 2, 3] & filteredList (· > 0) %~ (· * 2)
  result ≡ [2, 4, 6]

test "filteredList: collect filtered elements" := do
  let result := [-1, 2, -3, 4] ^.. filteredList (· > 0)
  result ≡ [2, 4]

test "filteredList: empty list" := do
  let result := ([] : List Int) & filteredList (· > 0) %~ (· * 2)
  result ≡ []

test "ifilteredList: modify even indices" := do
  let result := ["a", "b", "c", "d"] & ifilteredList (fun i _ => i % 2 == 0) %~ String.toUpper
  result ≡ ["A", "b", "C", "d"]

test "ifilteredList: filter by index and value" := do
  let result := [-1, 2, 3, -4] ^.. ifilteredList (fun i x => i < 2 && x > 0)
  result ≡ [2]

/-! ## List Operations: _head, _last, taking, dropping -/

test "_head: preview non-empty" := do
  let result := [1, 2, 3] ^? _head
  result ≡ (some 1)

test "_head: preview empty" := do
  let result := ([] : List Int) ^? _head
  result ≡ (none : Option Int)

test "_head: over non-empty" := do
  let result := [1, 2, 3] & _head %~ (· * 10)
  result ≡ [10, 2, 3]

test "_head: over empty" := do
  let result := ([] : List Int) & _head %~ (· * 10)
  result ≡ []

test "_head: set value" := do
  let result := [1, 2, 3] & _head .~ 100
  result ≡ [100, 2, 3]

test "_last: preview non-empty" := do
  let result := [1, 2, 3] ^? _last
  result ≡ (some 3)

test "_last: preview singleton" := do
  let result := [42] ^? _last
  result ≡ (some 42)

test "_last: preview empty" := do
  let result := ([] : List Int) ^? _last
  result ≡ (none : Option Int)

test "_last: over non-empty" := do
  let result := [1, 2, 3] & _last %~ (· * 10)
  result ≡ [1, 2, 30]

test "taking: first 2 elements" := do
  let result := [1, 2, 3, 4] & taking 2 %~ (· * 10)
  result ≡ [10, 20, 3, 4]

test "taking: take 0" := do
  let result := [1, 2, 3] & taking 0 %~ (· * 10)
  result ≡ [1, 2, 3]

test "taking: take more than length" := do
  let result := [1, 2] & taking 10 %~ (· * 10)
  result ≡ [10, 20]

test "taking: collect" := do
  let result := [1, 2, 3, 4, 5] ^.. taking 2
  result ≡ [1, 2]

test "dropping: skip first 2" := do
  let result := [1, 2, 3, 4] & dropping 2 %~ (· * 10)
  result ≡ [1, 2, 30, 40]

test "dropping: skip 0" := do
  let result := [1, 2, 3] & dropping 0 %~ (· * 10)
  result ≡ [10, 20, 30]

test "dropping: skip more than length" := do
  let result := [1, 2] & dropping 10 %~ (· * 10)
  result ≡ [1, 2]

test "dropping: collect" := do
  let result := [1, 2, 3, 4, 5] ^.. dropping 2
  result ≡ [3, 4, 5]

/-! ## Fold Enhancement Tests with Traversals -/

test "toListTraversal: basic" := do
  let result := [1, 2, 3] ^.. Collimator.Instances.List.traversed
  result ≡ [1, 2, 3]

test "toListTraversal: empty" := do
  let result := ([] : List Int) ^.. Collimator.Instances.List.traversed
  result ≡ []

/-! ## Prism Utility Tests -/

test "failing: preview always none" := do
  let failingPrism : Prism' Int String := failing
  let result := (42 : Int) ^? failingPrism
  result ≡ (none : Option String)

test "failing: over is identity" := do
  let failingPrism : Prism' Int Int := failing
  let result := 42 & failingPrism %~ (· * 2)
  result ≡ 42

test "prismFromPartial: even numbers" := do
  let evenPrism : Prism' Int Int := prismFromPartial
    (fun n : Int => if n % 2 == 0 then some n else none)
    _root_.id
  (4 ^? evenPrism) ≡ (some 4)
  (5 ^? evenPrism) ≡ none

test "prismFromPartial: review" := do
  let evenPrism : Prism' Int Int := prismFromPartial
    (fun n : Int => if n % 2 == 0 then some n else none)
    _root_.id
  (review' evenPrism 10) ≡ 10

/-! ## orElse Tests -/

test "orElse: first matches" := do
  let p1 : Prism' Int Int := prismFromPartial (fun n : Int => if n > 0 then some n else none) _root_.id
  let p2 : Prism' Int Int := prismFromPartial (fun n : Int => if n < 0 then some n else none) _root_.id
  let combined : AffineTraversal' Int Int := orElse p1 p2
  (5 ^? combined) ≡ (some 5)

test "orElse: second matches" := do
  let p1 : Prism' Int Int := prismFromPartial (fun n : Int => if n > 0 then some n else none) _root_.id
  let p2 : Prism' Int Int := prismFromPartial (fun n : Int => if n < 0 then some n else none) _root_.id
  let combined : AffineTraversal' Int Int := orElse p1 p2
  ((-3) ^? combined) ≡ (some (-3))

test "orElse: neither matches" := do
  let p1 : Prism' Int Int := prismFromPartial (fun n : Int => if n > 10 then some n else none) _root_.id
  let p2 : Prism' Int Int := prismFromPartial (fun n : Int => if n < -10 then some n else none) _root_.id
  let combined : AffineTraversal' Int Int := orElse p1 p2
  (0 ^? combined) ≡ (none : Option Int)

/-! ## Monomorphic Operator Tests -/

test "^. operator: view" := do
  let pair := (10, "hello")
  let lens : Lens' (Int × String) Int := _1
  let result := pair ^. lens
  result ≡ 10

test ".~ operator: set" := do
  let pair := (10, "hello")
  let lens : Lens' (Int × String) Int := _1
  let setter := lens .~ 99
  let result := setter pair
  result ≡ (99, "hello")

test "%~ operator: over" := do
  let pair := (10, "hello")
  let lens : Lens' (Int × String) Int := _1
  let modifier := lens %~ (· * 2)
  let result := modifier pair
  result ≡ (20, "hello")

test "^? operator: preview some" := do
  let opt : Option Int := some 42
  let result := opt ^? (somePrism' Int)
  result ≡ (some 42)

test "^? operator: preview none" := do
  let opt : Option Int := none
  let result := opt ^? (somePrism' Int)
  result ≡ none

/-! ## Helper Tests -/

private structure TestPoint where
  x : Int
  y : Int
  deriving BEq, Repr

test "first': explicit tuple lens" := do
  let pair := (10, "hello")
  let fstLens : Lens' (Int × String) Int := Helpers.first' Int String
  let result := pair ^. fstLens
  result ≡ 10

test "second': explicit tuple lens" := do
  let pair := (10, "hello")
  let sndLens : Lens' (Int × String) String := Helpers.second' Int String
  let result := pair ^. sndLens
  result ≡ "hello"

test "some': explicit option prism" := do
  let opt : Option Int := some 42
  let somePrism : Prism' (Option Int) Int := Helpers.some' Int
  let result := opt ^? somePrism
  result ≡ (some 42)

test "each': explicit list traversal" := do
  let lst := [1, 2, 3]
  let result := lst ^.. Helpers.each' Int
  result ≡ [1, 2, 3]

test "lensOf: build lens with explicit types" := do
  let xLens : Lens' TestPoint Int := Helpers.lensOf TestPoint Int (·.x) (fun p x => { p with x := x })
  let p := TestPoint.mk 10 20
  (p ^. xLens) ≡ 10
  (p & xLens .~ 99) ≡ (TestPoint.mk 99 20)

test "prismOf: build prism with explicit types" := do
  let positivePrism : Prism' Int Int := Helpers.prismOf Int Int _root_.id (fun n => if n > 0 then some n else none)
  (5 ^? positivePrism) ≡ (some 5)
  ((-3) ^? positivePrism) ≡ (none : Option Int)

/-! ## Advanced Filtered & Indexed Tests -/

-- Helper structures for lens composition tests
private structure Product where
  name : String
  price : Nat
  quantity : Nat
deriving Repr, BEq, Inhabited

private def priceLens : Lens' Product Nat :=
  lens' (fun p => p.price) (fun p newPrice => { p with price := newPrice })

private def quantityLens : Lens' Product Nat :=
  lens' (fun p => p.quantity) (fun p newQty => { p with quantity := newQty })

test "Filtered: basic predicate filtering" := do
  -- Filter evens, multiply by 10
  let input1 : List Nat := [1, 2, 3, 4, 5, 6]
  let result1 := input1 & filteredList (fun x => x % 2 == 0) %~ (· * 10)
  result1 ≡ [1, 20, 3, 40, 5, 60]

  -- Filter by range
  let input2 : List Nat := [5, 15, 25, 45, 55, 65]
  let result2 := input2 & filteredList (fun x => x > 10 && x < 50) %~ (· + 1000)
  result2 ≡ [5, 1015, 1025, 1045, 55, 65]

  -- Filter odds
  let result3 := input1 & filteredList (fun x => x % 2 == 1) %~ (· + 100)
  result3 ≡ [101, 2, 103, 4, 105, 6]

test "Filtered: edge cases" := do
  let evenFilter : Traversal' (List Nat) Nat := filteredList (fun x => x % 2 == 0)

  -- Empty list
  (([] : List Nat) & evenFilter %~ (· * 100)) ≡ ([] : List Nat)

  -- No matches
  let odds : List Nat := [1, 3, 5, 7]
  (odds & evenFilter %~ (· * 100)) ≡ odds

  -- All match
  let evens : List Nat := [2, 4, 6]
  (evens & evenFilter %~ (· * 100)) ≡ [200, 400, 600]

  -- Single element
  ([42] & evenFilter %~ (· + 10)) ≡ [52]
  ([43] & evenFilter %~ (· + 10)) ≡ [43]

test "Filtered: effectful traversals with Option" := do
  let evenFilter : Traversal' (List Nat) Nat := filteredList (fun x => x % 2 == 0)

  -- Validation that fails
  let input1 : List Nat := [1, 2, 3, 4, 5, 6]
  let failingValidator : Nat → Option Nat := fun x =>
    if x < 5 then some (x * 2) else none
  let optResult1 := Traversal.traverse' evenFilter failingValidator input1
  match optResult1 with
  | some _ => throw (IO.userError "Should fail on 6")
  | none => pure ()

  -- Validation that succeeds
  let input2 : List Nat := [1, 2, 3, 4, 5]
  let optResult2 := Traversal.traverse' evenFilter failingValidator input2
  match optResult2 with
  | none => throw (IO.userError "Should succeed")
  | some result => result ≡ [1, 4, 3, 8, 5]

test "Filtered: composition with lenses" := do
  let inventory : List Product := [
    { name := "Widget", price := 50, quantity := 10 },
    { name := "Gadget", price := 150, quantity := 5 },
    { name := "Premium", price := 200, quantity := 3 }
  ]

  -- Restock expensive items (price > 100)
  let expensive : Traversal' (List Product) Product := filteredList (fun p => p.price > 100)
  let expensiveQty : Traversal' (List Product) Nat := expensive ∘ quantityLens
  let restocked : List Product := inventory & expensiveQty %~ (· + 50)
  ensure (restocked[1]!.quantity == 55) "expensive restock gadget"
  ensure (restocked[2]!.quantity == 53) "expensive restock premium"
  ensure (restocked[0]!.quantity == 10) "widget unchanged"

  -- Apply discount to low stock items
  let lowStock : Traversal' (List Product) Product := filteredList (fun p => p.quantity < 10)
  let lowStockPrice : Traversal' (List Product) Nat := lowStock ∘ priceLens
  let discounted : List Product := inventory & lowStockPrice %~ (fun p => p * 80 / 100)
  ensure (discounted[1]!.price == 120) "discount gadget"
  ensure (discounted[2]!.price == 160) "discount premium"
  ensure (discounted[0]!.price == 50) "widget unchanged"

test "Indexed: access index and value" := do
  -- Modify even indices only
  let result1 := [1, 2, 3, 4, 5, 6] & ifilteredList (fun i _ => i % 2 == 0) %~ (· * 10)
  result1 ≡ [10, 2, 30, 4, 50, 6]

  -- Modify odd indices only
  let result2 := [1, 2, 3, 4, 5, 6] & ifilteredList (fun i _ => i % 2 == 1) %~ (· + 100)
  result2 ≡ [1, 102, 3, 104, 5, 106]

  -- First 3 elements
  let result3 := [1, 2, 3, 4, 5, 6] & ifilteredList (fun i _ => i < 3) %~ (· * 10)
  result3 ≡ [10, 20, 30, 4, 5, 6]

test "Indexed: focus single element with ix" := do
  let input : List Nat := [10, 20, 30, 40, 50]

  -- Modify element at index 3
  let result1 := input & ix 3 %~ (· * 10)
  result1 ≡ [10, 20, 30, 400, 50]

  -- Out of bounds (no-op)
  let result2 := input & ix 10 %~ (· * 999)
  result2 ≡ input

  -- ix on empty
  let result3 := ([] : List Nat) & ix 0 %~ (· + 100)
  result3 ≡ ([] : List Nat)

  -- Multiple ix operations
  let result4 := input
    |> (· & ix 0 %~ (· + 10))
    |> (· & ix 2 %~ (· + 20))
    |> (· & ix 4 %~ (· + 30))
  result4 ≡ [20, 20, 50, 40, 80]

test "Indexed: optional access with atLens" := do
  let input : List Nat := [10, 20, 30, 40, 50]
  let at2 : Lens' (List Nat) (Option Nat) := atLens 2
  let at10 : Lens' (List Nat) (Option Nat) := atLens 10
  let at0 : Lens' (List Nat) (Option Nat) := atLens 0
  let at1 : Lens' (List Nat) (Option Nat) := atLens 1

  -- View at valid/invalid indices
  (input ^. at2) ≡ (some 30)
  (input ^. at10) ≡ (none : Option Nat)
  (([] : List Nat) ^. at0) ≡ (none : Option Nat)

  -- Set at valid index
  (input & at2 .~ some 300) ≡ [10, 20, 300, 40, 50]

  -- Set out of bounds (no-op)
  (input & at10 .~ some 999) ≡ input

  -- Over with Option.map
  let result : List Nat := input & at1 %~ Option.map (· * 10)
  result ≡ [10, 200, 30, 40, 50]

test "Combined: complex index+value predicates" := do
  let input : List Nat := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

  -- Even values at odd indices
  let result1 := input & ifilteredList (fun i v => i % 2 == 1 && v % 2 == 0) %~ (· * 100)
  result1 ≡ [1, 200, 3, 400, 5, 600, 7, 800, 9, 1000]

  -- Values greater than their index
  let input2 : List Nat := [0, 5, 1, 8, 2, 10, 3]
  let result2 := input2 & ifilteredList (fun i v => v > i) %~ (· * 2)
  result2 ≡ [0, 10, 1, 16, 2, 20, 3]

  -- Value == index^2 (perfect squares)
  let squares : List Nat := [0, 1, 4, 9, 16, 25, 36]
  let result3 := squares & ifilteredList (fun i v => v == i * i) %~ (· + 1000)
  result3 ≡ [1000, 1001, 1004, 1009, 1016, 1025, 1036]

test "Stateful: counting and accumulation" := do
  let input : List Nat := [1, 2, 3, 4, 5, 6]
  let evens : Traversal' (List Nat) Nat := filteredList (fun x => x % 2 == 0)

  -- Count matching elements
  let counter (x : Nat) : StateT Nat Id Nat := do
    let count ← get
    set (count + 1)
    pure x
  let (_, count) := (Traversal.traverse' evens counter input).run 0
  count ≡ 3

  -- Accumulate sum
  let accumulator (x : Nat) : StateT Nat Id Nat := do
    let sum ← get
    set (sum + x)
    pure x
  let (_, sum) := (Traversal.traverse' evens accumulator input).run 0
  sum ≡ 12

  -- Running sum (using unfiltered list)
  let input2 : List Nat := [1, 2, 3, 4, 5]
  let tr : Traversal' (List Nat) Nat := Instances.List.traversed
  let runningSum (x : Nat) : StateT Nat Id Nat := do
    let s ← get
    let newSum := s + x
    set newSum
    pure newSum
  let (result, _) := (Traversal.traverse' tr runningSum input2).run 0
  result ≡ [1, 3, 6, 10, 15]

  -- Assign IDs only to filtered elements
  let input3 : List Nat := [1, 2, 3, 4, 5, 6, 7, 8]
  let idAssigner (_ : Nat) : StateT Nat Id Nat := do
    let id ← get
    set (id + 1)
    pure id
  let (result3, _) := (Traversal.traverse' evens idAssigner input3).run 100
  result3 ≡ [1, 100, 3, 101, 5, 102, 7, 103]

test "Real-world: selective array updates" := do
  -- Increment at even positions
  let result1 := [1, 2, 3, 4, 5, 6, 7, 8] & ifilteredList (fun i _ => i % 2 == 0) %~ (· + 10)
  result1 ≡ [11, 2, 13, 4, 15, 6, 17, 8]

  -- Zero out negatives
  let input2 : List Int := [-5, 10, -3, 0, 7, -2, 15]
  let result2 := input2 & filteredList (fun x : Int => x < 0) %~ (fun _ => 0)
  result2 ≡ [0, 10, 0, 0, 7, 0, 15]

  -- Clamp large values
  let input3 : List Nat := [10, 150, 30, 200, 50, 180]
  let result3 := input3 & filteredList (fun x : Nat => x > 100) %~ (fun _ => 100)
  result3 ≡ [10, 100, 30, 100, 50, 100]

test "Real-world: conditional batch operations" := do
  let inventory : List Product := [
    { name := "Widget", price := 50, quantity := 10 },
    { name := "Gadget", price := 150, quantity := 5 },
    { name := "Premium", price := 200, quantity := 3 },
    { name := "Basic", price := 25, quantity := 20 }
  ]

  -- 20% discount on expensive items (price > 100)
  let expensive : Traversal' (List Product) Product := filteredList (fun p => p.price > 100)
  let expensivePrice : Traversal' (List Product) Nat := expensive ∘ priceLens
  let discounted : List Product := inventory & expensivePrice %~ (fun p => p * 80 / 100)
  ensure (discounted[1]!.price == 120) "discount gadget"
  ensure (discounted[2]!.price == 160) "discount premium"
  ensure (discounted[0]!.price == 50) "widget unchanged"

  -- 10% tax on low stock (quantity < 10)
  let lowStock : Traversal' (List Product) Product := filteredList (fun p => p.quantity < 10)
  let lowStockPrice : Traversal' (List Product) Nat := lowStock ∘ priceLens
  let taxed : List Product := inventory & lowStockPrice %~ (fun p => p * 110 / 100)
  ensure (taxed[1]!.price == 165) "tax gadget"
  ensure (taxed[2]!.price == 220) "tax premium"

test "Real-world: sparse array operations" := do
  let input : List Nat := [0, 5, 0, 0, 3, 0, 7, 0]
  let nonZero : Traversal' (List Nat) Nat := filteredList (fun x => x != 0)

  -- Double non-zero elements
  (input & nonZero %~ (· * 2)) ≡ [0, 10, 0, 0, 6, 0, 14, 0]

  -- Normalize to 1
  (input & nonZero %~ (fun _ => 1)) ≡ [0, 1, 0, 0, 1, 0, 1, 0]

  -- Non-zero at even indices
  let input2 : List Nat := [0, 5, 10, 0, 20, 0, 30, 0]
  let result := input2 & ifilteredList (fun i v => v != 0 && i % 2 == 0) %~ (· + 1000)
  result ≡ [0, 5, 1010, 0, 1020, 0, 1030, 0]

test "Performance: short-circuiting with Option" := do
  let tr : Traversal' (List Nat) Nat := Instances.List.traversed

  -- Short-circuit on invalid
  let evenValidator : Nat → Option Nat := fun x =>
    if x % 2 == 0 then some x else none
  let invalid : List Nat := [2, 4, 6, 7, 8, 10]
  match Traversal.traverse' tr evenValidator invalid with
  | some _ => throw (IO.userError "Should short-circuit")
  | none => pure ()

  -- Successful validation
  let valid : List Nat := [2, 4, 6, 8, 10]
  match Traversal.traverse' tr evenValidator valid with
  | none => throw (IO.userError "Should succeed")
  | some r => r ≡ valid

  -- Combined filter
  let input : List Nat := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
  let evenLarge : Traversal' (List Nat) Nat := ifilteredList (fun _ v => v % 2 == 0 && v > 5)
  let result := input & evenLarge %~ (· * 10)
  result ≡ [1, 2, 3, 4, 5, 60, 7, 80, 9, 100]

test "Composition: reusable and higher-order filters" := do
  let input : List Nat := [1, 2, 3, 4, 5, 6]

  -- Reusable evens filter with different transforms
  let evens : Traversal' (List Nat) Nat := filteredList (fun x => x % 2 == 0)
  (input & evens %~ (· * 2)) ≡ [1, 4, 3, 8, 5, 12]
  (input & evens %~ (· + 100)) ≡ [1, 102, 3, 104, 5, 106]

  -- Negated filter (NOT even = odd)
  let notEven : Traversal' (List Nat) Nat := filteredList (fun x => x % 2 != 0)
  (input & notEven %~ (· + 10)) ≡ [11, 2, 13, 4, 15, 6]

  -- Union: even OR > 4
  let union : Traversal' (List Nat) Nat := filteredList (fun x => x % 2 == 0 || x > 4)
  (input & union %~ (· * 10)) ≡ [1, 20, 3, 40, 50, 60]

  -- Intersection: even AND > 3
  let intersection : Traversal' (List Nat) Nat := filteredList (fun x => x % 2 == 0 && x > 3)
  (input & intersection %~ (· + 100)) ≡ [1, 2, 3, 104, 5, 106]

/-! ## String Optics Tests -/

test "String.chars: iso to List Char" := do
  let s := "hello"
  let charsIso : Iso' String (List Char) := chars
  let cs := s ^. charsIso
  cs ≡ ['h', 'e', 'l', 'l', 'o']
  let s' := review' charsIso ['w', 'o', 'r', 'l', 'd']
  s' ≡ "world"

test "String.traversed: modify all characters" := do
  let s := "abc"
  let result := s & Collimator.Instances.String.traversed %~ Char.toUpper
  result ≡ "ABC"

test "String.traversed: collect characters" := do
  let s := "xyz"
  let cs := s ^.. Collimator.Instances.String.traversed
  cs ≡ ['x', 'y', 'z']

test "String.itraversed: indexed access" := do
  let s := "abc"
  let indexed := s ^.. Collimator.Instances.String.itraversed
  indexed ≡ [(0, 'a'), (1, 'b'), (2, 'c')]

test "String HasAt: valid index" := do
  let s := "hello"
  let c := s ^. atLens (ι := Nat) (s := String) (a := Char) 1
  c ≡ (some 'e')

test "String HasAt: invalid index" := do
  let s := "hi"
  let c := s ^. atLens (ι := Nat) (s := String) (a := Char) 10
  c ≡ none

test "String HasIx: modify at index" := do
  let s := "cat"
  let result := s & ix (ι := Nat) (s := String) (a := Char) 1 %~ (fun _ => 'o')
  result ≡ "cot"

test "String HasIx: out of bounds is no-op" := do
  let s := "dog"
  let result := s & ix (ι := Nat) (s := String) (a := Char) 100 %~ (fun _ => 'x')
  result ≡ "dog"

/-! ## Bifunctor Traversal Tests -/

test "both: traverse both components of pair" := do
  let pair := (3, 5)
  let result := pair & both %~ (· * 2)
  result ≡ (6, 10)

test "both: collect both values" := do
  let pair := ("a", "b")
  let result := pair ^.. both
  result ≡ ["a", "b"]

test "both': monomorphic version" := do
  let pair := (10, 20)
  let result := pair & both' Int %~ (· + 1)
  result ≡ (11, 21)

test "chosen: traverse left branch" := do
  let s : Sum Int Int := Sum.inl 42
  let result := s & chosen %~ (· * 2)
  result ≡ (Sum.inl 84)

test "chosen: traverse right branch" := do
  let s : Sum Int Int := Sum.inr 99
  let result := s & chosen %~ (· + 1)
  result ≡ (Sum.inr 100)

test "chosen: collect from either branch" := do
  let left : Sum String String := Sum.inl "hello"
  let right : Sum String String := Sum.inr "world"
  let l := left ^.. chosen
  let r := right ^.. chosen
  l ≡ ["hello"]
  r ≡ ["world"]

test "chosen': monomorphic version" := do
  let s : Sum Int Int := Sum.inl 5
  let result := s & chosen' Int %~ (· * 10)
  result ≡ (Sum.inl 50)

test "swapped: swap pair components" := do
  let pair := (1, 2)
  let swappedIso : Iso' (Int × Int) (Int × Int) := swapped
  let result := pair ^. swappedIso
  result ≡ (2, 1)

test "swappedSum: swap sum branches" := do
  let left : Sum Int Int := Sum.inl 42
  let right : Sum Int Int := Sum.inr 99
  let swappedSumIso : Iso' (Sum Int Int) (Sum Int Int) := swappedSum
  let l' := left ^. swappedSumIso
  let r' := right ^. swappedSumIso
  l' ≡ (Sum.inr 42)
  r' ≡ (Sum.inl 99)

test "beside: traverse both sides of pair" := do
  let pair := ([1, 2], [3, 4])
  let listTrav : Traversal' (List Int) Int := Collimator.Instances.List.traversed
  let t : Traversal' (List Int × List Int) Int := beside listTrav listTrav
  let result := pair & t %~ (· + 1)
  result ≡ ([2, 3], [4, 5])

test "beside: collect from both sides" := do
  let pair := (["a", "b"], ["c"])
  let listTrav : Traversal' (List String) String := Collimator.Instances.List.traversed
  let t : Traversal' (List String × List String) String := beside listTrav listTrav
  let result := pair ^.. t
  result ≡ ["a", "b", "c"]

test "beside': monomorphic version" := do
  let pair := ([10, 20], [30])
  let listTrav : Traversal' (List Int) Int := Collimator.Instances.List.traversed
  let t : Traversal' (List Int × List Int) Int := beside' listTrav listTrav
  let result := pair & t %~ (· * 2)
  result ≡ ([20, 40], [60])

test "beside: heterogeneous source types" := do
  -- Left is Option, right is List
  let pair : (Option Int × List Int) := (some 5, [1, 2])
  let optTrav : Traversal' (Option Int) Int := Collimator.traversal
    (fun {F} [Applicative F] (f : Int → F Int) (opt : Option Int) =>
      match opt with
      | none => pure none
      | some x => Functor.map some (f x))
  let listTrav : Traversal' (List Int) Int := Collimator.Instances.List.traversed
  let t : Traversal' (Option Int × List Int) Int := beside optTrav listTrav
  let result := pair & t %~ (· + 10)
  result ≡ (some 15, [11, 12])

/-! ## Plated Tests -/

-- Simple tree for testing Plated
private inductive SimpleTree where
  | leaf : Int → SimpleTree
  | node : SimpleTree → SimpleTree → SimpleTree
deriving BEq, Repr

private instance : Plated SimpleTree where
  plate := Collimator.traversal
    (fun {F : Type → Type} [Applicative F]
      (f : SimpleTree → F SimpleTree) (t : SimpleTree) =>
        match t with
        | SimpleTree.leaf _ => pure t
        | SimpleTree.node l r => pure SimpleTree.node <*> f l <*> f r)

private def sumLeaves : SimpleTree → Int
  | SimpleTree.leaf n => n
  | SimpleTree.node l r => sumLeaves l + sumLeaves r

test "Plated List: children of list" := do
  let xs := [1, 2, 3, 4]
  let cs := childrenOf xs
  -- List's plate focuses on the tail
  cs ≡ [[2, 3, 4]]

test "Plated List: overChildren" := do
  let xs := [1, 2, 3]
  -- Reverse the tail
  let result := overChildren List.reverse xs
  result ≡ [1, 3, 2]

test "Plated Option: no children" := do
  let x : Option Int := some 42
  let cs := childrenOf x
  cs ≡ ([] : List (Option Int))

test "Plated SimpleTree: children of node" := do
  let leaf1 := SimpleTree.leaf 1
  let leaf2 := SimpleTree.leaf 2
  let tree := SimpleTree.node leaf1 leaf2
  let cs := childrenOf tree
  cs.length ≡ 2

test "Plated SimpleTree: children of leaf" := do
  let leaf := SimpleTree.leaf 42
  let cs := childrenOf leaf
  cs ≡ ([] : List SimpleTree)

test "transform: bottom-up transformation" := do
  let leaf1 := SimpleTree.leaf 1
  let leaf2 := SimpleTree.leaf 2
  let tree := SimpleTree.node leaf1 leaf2
  -- Double all leaf values
  let doubleLeaves : SimpleTree → SimpleTree
    | SimpleTree.leaf n => SimpleTree.leaf (n * 2)
    | t => t
  let result := transform doubleLeaves tree
  (sumLeaves result) ≡ 6  -- (1*2) + (2*2) = 6

test "universeList: collect all nodes" := do
  let leaf1 := SimpleTree.leaf 1
  let leaf2 := SimpleTree.leaf 2
  let tree := SimpleTree.node leaf1 leaf2
  let all := universeList tree
  -- Should include root + 2 leaves = 3 nodes
  all.length ≡ 3

test "cosmosCount: count all nodes" := do
  let leaf1 := SimpleTree.leaf 1
  let leaf2 := SimpleTree.leaf 2
  let inner := SimpleTree.node leaf1 leaf2
  let tree := SimpleTree.node inner (SimpleTree.leaf 3)
  -- Tree structure: node(node(leaf, leaf), leaf) = 5 nodes
  (cosmosCount tree) ≡ 5

test "depth: measure tree depth" := do
  let leaf := SimpleTree.leaf 1
  (depth leaf) ≡ 1
  let shallow := SimpleTree.node leaf leaf
  (depth shallow) ≡ 2
  let deep := SimpleTree.node shallow leaf
  (depth deep) ≡ 3

test "allOf: check all nodes" := do
  let tree := SimpleTree.node (SimpleTree.leaf 2) (SimpleTree.leaf 4)
  let isEvenLeaf : SimpleTree → Bool
    | SimpleTree.leaf n => n % 2 == 0
    | _ => true
  ensure (allOf isEvenLeaf tree) "all leaves even"

test "anyOf: check any node" := do
  let tree := SimpleTree.node (SimpleTree.leaf 1) (SimpleTree.leaf 2)
  let isTwo : SimpleTree → Bool
    | SimpleTree.leaf 2 => true
    | _ => false
  ensure (anyOf isTwo tree) "found a two"

test "findOf: find matching node" := do
  let tree := SimpleTree.node (SimpleTree.leaf 1) (SimpleTree.leaf 42)
  let is42 : SimpleTree → Bool
    | SimpleTree.leaf 42 => true
    | _ => false
  let found := findOf is42 tree
  ensure found.isSome "found 42"

test "rewrite: iterative rewriting" := do
  -- Rewrite nested nodes to simplify
  let leaf := SimpleTree.leaf 1
  let tree := SimpleTree.node leaf leaf
  -- Rewrite: if both children are the same leaf, collapse to that leaf
  let simplify : SimpleTree → Option SimpleTree
    | SimpleTree.node (SimpleTree.leaf n) (SimpleTree.leaf m) =>
        if n == m then some (SimpleTree.leaf n) else none
    | _ => none
  let result := rewrite simplify tree
  -- node(leaf 1, leaf 1) should become leaf 1
  result ≡ (SimpleTree.leaf 1)

/-! ## HashMap and AssocList Tests -/

open Collimator.Instances.HashMap
open Collimator.Instances.AssocList

test "HashMap HasAt: lookup existing key" := do
  let m : Std.HashMap String Nat := (∅ : Std.HashMap String Nat).insert "a" 1 |>.insert "b" 2
  let result := m ^. atLens (a := Nat) "a"
  result ≡ (some 1)

test "HashMap HasAt: lookup missing key" := do
  let m : Std.HashMap String Nat := (∅ : Std.HashMap String Nat).insert "a" 1
  let result := m ^. atLens (a := Nat) "b"
  result ≡ none

test "HashMap HasAt: update value" := do
  let m : Std.HashMap String Nat := (∅ : Std.HashMap String Nat).insert "a" 1
  let m' := m & atLens (a := Nat) "a" .~ some 100
  (m' ^. atLens (a := Nat) "a") ≡ (some 100)

test "HashMap HasAt: insert new key" := do
  let m : Std.HashMap String Nat := ∅
  let m' := m & atLens (a := Nat) "new" .~ some 42
  (m' ^. atLens (a := Nat) "new") ≡ (some 42)

test "HashMap HasAt: delete by setting none" := do
  let m : Std.HashMap String Nat := (∅ : Std.HashMap String Nat).insert "a" 1
  let m' := m & atLens (a := Nat) "a" .~ none
  (m' ^. atLens (a := Nat) "a") ≡ none

test "HashMap HasIx: modify existing" := do
  let m : Std.HashMap String Nat := (∅ : Std.HashMap String Nat).insert "x" 10
  let m' := m & ix (a := Nat) "x" %~ (· + 5)
  (m'.get? "x") ≡ (some 15)

test "HashMap HasIx: no-op on missing" := do
  let m : Std.HashMap String Nat := (∅ : Std.HashMap String Nat).insert "x" 10
  let m' := m & ix (a := Nat) "y" %~ (· + 5)
  m'.size ≡ 1

test "AssocList HasAt: lookup existing key" := do
  let xs : AssocList String Nat := AssocList.cons "a" 1 (AssocList.cons "b" 2 AssocList.nil)
  let result := xs ^. atLens (a := Nat) "a"
  result ≡ (some 1)

test "AssocList HasAt: lookup missing key" := do
  let xs : AssocList String Nat := AssocList.cons "a" 1 AssocList.nil
  let result := xs ^. atLens (a := Nat) "b"
  result ≡ none

test "AssocList HasAt: update value" := do
  let xs : AssocList String Nat := AssocList.cons "a" 1 AssocList.nil
  let xs' := xs & atLens (a := Nat) "a" .~ some 100
  (xs' ^. atLens (a := Nat) "a") ≡ (some 100)

test "AssocList HasAt: insert new key" := do
  let xs : AssocList String Nat := AssocList.nil
  let xs' := xs & atLens (a := Nat) "new" .~ some 42
  (xs' ^. atLens (a := Nat) "new") ≡ (some 42)

test "AssocList HasIx: modify existing" := do
  let xs : AssocList String Nat := AssocList.cons "x" 10 AssocList.nil
  let xs' := xs & ix (a := Nat) "x" %~ (· + 5)
  (xs'.find? "x") ≡ (some 15)

test "AssocList HasIx: no-op on missing" := do
  let xs : AssocList String Nat := AssocList.cons "x" 10 AssocList.nil
  let xs' := xs & ix (a := Nat) "y" %~ (· + 5)
  xs'.toList.length ≡ 1

end CollimatorTests.CombinatorTests
