import Batteries
import Collimator.Combinators
import Collimator.Operators
import Collimator.Instances
import Collimator.Optics
import Collimator.Concrete.FunArrow
import Collimator.Prelude
import Collimator.Helpers
import CollimatorTests.Framework

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
open Collimator.Combinators.Plated
open CollimatorTests

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
  ensureEq "view" 10 (p ^. scoreLens)
  let updated := p & scoreLens %~ (· + 5)
  ensureEq "over" 15 (updated ^. scoreLens)
  let reset := p & scoreLens .~ 0
  ensureEq "set" 0 (reset ^. scoreLens)

test "product instances supply convenient lenses" := do
  let pair := (3, true)
  let firstLens : Lens' (Int × Bool) Int :=
    Collimator.Instances.Prod.first (α := Int) (β := Bool) (γ := Int)
  let secondLens : Lens' (Int × Bool) Bool :=
    Collimator.Instances.Prod.second (α := Int) (β := Bool) (γ := Bool)
  let bumpedFirst := pair & firstLens %~ (· + 1)
  ensureEq "bump first" (4, true) bumpedFirst
  let toggled := pair & secondLens %~ not
  ensureEq "toggle second" (3, false) toggled
  let triple : (Int × Int) × Int := ((1, 2), 3)
  let lens : Lens' ((Int × Int) × Int) Int :=
    Collimator.Instances.Prod.firstOfTriple (α := Int) (β := Int) (γ := Int) (δ := Int)
  let incremented := triple & lens %~ (· + 10)
  ensureEq "first of triple" ((11, 2), 3) incremented

test "sum prisms preview and review branches" := do
  let leftPrism : Prism (Sum Int String) (Sum Int String) Int Int :=
    Collimator.Instances.Sum.left
      (α := Int) (β := String) (γ := Int)
  let inLeft : Sum Int String := Sum.inl (7 : Int)
  let inRight : Sum Int String := Sum.inr (α := Int) ("optics" : String)
  ensureEq "preview left" (some (7 : Int)) (inLeft ^? leftPrism)
  ensureEq "preview right" (none : Option Int) (inRight ^? leftPrism)
  let expectedReview : Sum Int String := Sum.inl (5 : Int)
  ensureEq "review" expectedReview (review' leftPrism (5 : Int))

test "option prisms distinguish some and none" := do
  let somePrism : Prism (Option Int) (Option Int) Int Int :=
    Collimator.Instances.Option.somePrism (α := Int) (β := Int)
  ensureEq "preview some" (some 9) ((some 9) ^? somePrism)
  ensureEq "preview none" (none : Option Int) (none ^? somePrism)
  ensureEq "review some" (some 4) (review' somePrism 4)

test "list ix updates element at index" := do
  let elements := [10, 20, 30]
  let traversal : Traversal' (List Int) Int :=
    ix (ι := Nat) (s := List Int) (a := Int) 1
  let updated := elements & traversal %~ (· + 7)
  ensureEq "ix modifies" [10, 27, 30] updated

test "list at lens views optional element" := do
  let xs := ["lean", "optic", "library"]
  let l : Lens' (List String) (Option String) :=
    atLens (ι := Nat) (s := List String) (a := String) 2
  ensureEq "get existing" (some "library") (xs ^. l)
  ensureEq "missing" (none : Option String) (["lean"] ^. l)

test "array ix modifies in-bounds value and ignores out-of-bounds" := do
  let arr : Array Int := #[1, 2, 3]
  let traversal : Traversal' (Array Int) Int :=
    ix (ι := Nat) (s := Array Int) (a := Int) 0
  let updated := arr & traversal %~ (· * 2)
  ensureEq "modify first" #[2, 2, 3] updated
  let untouched := arr & (ix (ι := Nat) (s := Array Int) (a := Int) 5) %~ (· + 1)
  ensureEq "oob" #[1, 2, 3] untouched

test "filtered traversal only updates predicate matches" := do
  let tr : Traversal' (List Int) Int :=
    Collimator.Instances.List.traversed (α := Int) (β := Int)
  let evens : Traversal' (List Int) Int :=
    filtered tr (fun n => n % 2 == 0)
  let result := [1, 2, 3, 4] & evens %~ (· + 1)
  ensureEq "filtered update" [1, 3, 3, 5] result

test "itraversed exposes index during updates" := do
  let base : Traversal' (List Int) (Nat × Int) :=
    Collimator.Instances.List.itraversed
  let bumped := [5, 5, 5] & base %~ (fun | (idx, v) => (idx, v + idx))
  ensureEq "index applied" [5, 6, 7] bumped

/-! ## filteredList and ifilteredList Tests -/

test "filteredList: double only positive numbers" := do
  let result := [-1, 2, -3, 4] & filteredList (· > 0) %~ (· * 2)
  ensureEq "positive doubled" [-1, 4, -3, 8] result

test "filteredList: filter none" := do
  let result := [1, 2, 3] & filteredList (· > 100) %~ (· * 2)
  ensureEq "none match" [1, 2, 3] result

test "filteredList: filter all" := do
  let result := [1, 2, 3] & filteredList (· > 0) %~ (· * 2)
  ensureEq "all match" [2, 4, 6] result

test "filteredList: collect filtered elements" := do
  let result := [-1, 2, -3, 4] ^.. filteredList (· > 0)
  ensureEq "collect positives" [2, 4] result

test "filteredList: empty list" := do
  let result := ([] : List Int) & filteredList (· > 0) %~ (· * 2)
  ensureEq "empty list unchanged" [] result

test "ifilteredList: modify even indices" := do
  let result := ["a", "b", "c", "d"] & ifilteredList (fun i _ => i % 2 == 0) %~ String.toUpper
  ensureEq "even indices uppercase" ["A", "b", "C", "d"] result

test "ifilteredList: filter by index and value" := do
  let result := [-1, 2, 3, -4] ^.. ifilteredList (fun i x => i < 2 && x > 0)
  ensureEq "index < 2 and value > 0" [2] result

/-! ## List Operations: _head, _last, taking, dropping -/

test "_head: preview non-empty" := do
  let result := [1, 2, 3] ^? _head
  ensureEq "head is 1" (some 1) result

test "_head: preview empty" := do
  let result := ([] : List Int) ^? _head
  ensureEq "head is none" (none : Option Int) result

test "_head: over non-empty" := do
  let result := [1, 2, 3] & _head %~ (· * 10)
  ensureEq "head modified" [10, 2, 3] result

test "_head: over empty" := do
  let result := ([] : List Int) & _head %~ (· * 10)
  ensureEq "empty unchanged" [] result

test "_head: set value" := do
  let result := [1, 2, 3] & _head .~ 100
  ensureEq "head set" [100, 2, 3] result

test "_last: preview non-empty" := do
  let result := [1, 2, 3] ^? _last
  ensureEq "last is 3" (some 3) result

test "_last: preview singleton" := do
  let result := [42] ^? _last
  ensureEq "single element" (some 42) result

test "_last: preview empty" := do
  let result := ([] : List Int) ^? _last
  ensureEq "last is none" (none : Option Int) result

test "_last: over non-empty" := do
  let result := [1, 2, 3] & _last %~ (· * 10)
  ensureEq "last modified" [1, 2, 30] result

test "taking: first 2 elements" := do
  let result := [1, 2, 3, 4] & taking 2 %~ (· * 10)
  ensureEq "first 2 modified" [10, 20, 3, 4] result

test "taking: take 0" := do
  let result := [1, 2, 3] & taking 0 %~ (· * 10)
  ensureEq "none modified" [1, 2, 3] result

test "taking: take more than length" := do
  let result := [1, 2] & taking 10 %~ (· * 10)
  ensureEq "all modified" [10, 20] result

test "taking: collect" := do
  let result := [1, 2, 3, 4, 5] ^.. taking 2
  ensureEq "first 2 collected" [1, 2] result

test "dropping: skip first 2" := do
  let result := [1, 2, 3, 4] & dropping 2 %~ (· * 10)
  ensureEq "last 2 modified" [1, 2, 30, 40] result

test "dropping: skip 0" := do
  let result := [1, 2, 3] & dropping 0 %~ (· * 10)
  ensureEq "all modified" [10, 20, 30] result

test "dropping: skip more than length" := do
  let result := [1, 2] & dropping 10 %~ (· * 10)
  ensureEq "none modified" [1, 2] result

test "dropping: collect" := do
  let result := [1, 2, 3, 4, 5] ^.. dropping 2
  ensureEq "last 3 collected" [3, 4, 5] result

/-! ## Fold Enhancement Tests with Traversals -/

test "toListTraversal: basic" := do
  let result := [1, 2, 3] ^.. Collimator.Instances.List.traversed
  ensureEq "collect all" [1, 2, 3] result

test "toListTraversal: empty" := do
  let result := ([] : List Int) ^.. Collimator.Instances.List.traversed
  ensureEq "empty list" [] result

/-! ## Prism Utility Tests -/

test "failing: preview always none" := do
  let failingPrism : Prism' Int String := failing
  let result := (42 : Int) ^? failingPrism
  ensureEq "always fails" (none : Option String) result

test "failing: over is identity" := do
  let failingPrism : Prism' Int Int := failing
  let result := 42 & failingPrism %~ (· * 2)
  ensureEq "unchanged" 42 result

test "prismFromPartial: even numbers" := do
  let evenPrism : Prism' Int Int := prismFromPartial
    (fun n : Int => if n % 2 == 0 then some n else none)
    _root_.id
  ensureEq "4 is even" (some 4) (4 ^? evenPrism)
  ensureEq "5 is odd" none (5 ^? evenPrism)

test "prismFromPartial: review" := do
  let evenPrism : Prism' Int Int := prismFromPartial
    (fun n : Int => if n % 2 == 0 then some n else none)
    _root_.id
  ensureEq "review returns value" 10 (review' evenPrism 10)

/-! ## orElse Tests -/

test "orElse: first matches" := do
  let p1 : Prism' Int Int := prismFromPartial (fun n : Int => if n > 0 then some n else none) _root_.id
  let p2 : Prism' Int Int := prismFromPartial (fun n : Int => if n < 0 then some n else none) _root_.id
  let combined : AffineTraversal' Int Int := orElse p1 p2
  ensureEq "positive wins" (some 5) (5 ^? combined)

test "orElse: second matches" := do
  let p1 : Prism' Int Int := prismFromPartial (fun n : Int => if n > 0 then some n else none) _root_.id
  let p2 : Prism' Int Int := prismFromPartial (fun n : Int => if n < 0 then some n else none) _root_.id
  let combined : AffineTraversal' Int Int := orElse p1 p2
  ensureEq "negative wins" (some (-3)) ((-3) ^? combined)

test "orElse: neither matches" := do
  let p1 : Prism' Int Int := prismFromPartial (fun n : Int => if n > 10 then some n else none) _root_.id
  let p2 : Prism' Int Int := prismFromPartial (fun n : Int => if n < -10 then some n else none) _root_.id
  let combined : AffineTraversal' Int Int := orElse p1 p2
  ensureEq "zero fails both" (none : Option Int) (0 ^? combined)

/-! ## Monomorphic Operator Tests -/

test "^. operator: view" := do
  let pair := (10, "hello")
  let lens : Lens' (Int × String) Int := _1
  let result := pair ^. lens
  ensureEq "view first" 10 result

test ".~ operator: set" := do
  let pair := (10, "hello")
  let lens : Lens' (Int × String) Int := _1
  let setter := lens .~ 99
  let result := setter pair
  ensureEq "set first" (99, "hello") result

test "%~ operator: over" := do
  let pair := (10, "hello")
  let lens : Lens' (Int × String) Int := _1
  let modifier := lens %~ (· * 2)
  let result := modifier pair
  ensureEq "double first" (20, "hello") result

test "^? operator: preview some" := do
  let opt : Option Int := some 42
  let result := opt ^? (somePrism' Int)
  ensureEq "preview some" (some 42) result

test "^? operator: preview none" := do
  let opt : Option Int := none
  let result := opt ^? (somePrism' Int)
  ensureEq "preview none" none result

/-! ## Helper Tests -/

private structure TestPoint where
  x : Int
  y : Int
  deriving BEq, Repr

test "first': explicit tuple lens" := do
  let pair := (10, "hello")
  let fstLens : Lens' (Int × String) Int := Helpers.first' Int String
  let result := pair ^. fstLens
  ensureEq "view first" 10 result

test "second': explicit tuple lens" := do
  let pair := (10, "hello")
  let sndLens : Lens' (Int × String) String := Helpers.second' Int String
  let result := pair ^. sndLens
  ensureEq "view second" "hello" result

test "some': explicit option prism" := do
  let opt : Option Int := some 42
  let somePrism : Prism' (Option Int) Int := Helpers.some' Int
  let result := opt ^? somePrism
  ensureEq "preview some" (some 42) result

test "each': explicit list traversal" := do
  let lst := [1, 2, 3]
  let result := lst ^.. Helpers.each' Int
  ensureEq "collect all" [1, 2, 3] result

test "lensOf: build lens with explicit types" := do
  let xLens : Lens' TestPoint Int := Helpers.lensOf TestPoint Int (·.x) (fun p x => { p with x := x })
  let p := TestPoint.mk 10 20
  ensureEq "view x" 10 (p ^. xLens)
  ensureEq "set x" (TestPoint.mk 99 20) (p & xLens .~ 99)

test "prismOf: build prism with explicit types" := do
  let positivePrism : Prism' Int Int := Helpers.prismOf Int Int _root_.id (fun n => if n > 0 then some n else none)
  ensureEq "positive matches" (some 5) (5 ^? positivePrism)
  ensureEq "negative fails" (none : Option Int) ((-3) ^? positivePrism)

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
  ensureEq "even filter" [1, 20, 3, 40, 5, 60] result1

  -- Filter by range
  let input2 : List Nat := [5, 15, 25, 45, 55, 65]
  let result2 := input2 & filteredList (fun x => x > 10 && x < 50) %~ (· + 1000)
  ensureEq "range filter" [5, 1015, 1025, 1045, 55, 65] result2

  -- Filter odds
  let result3 := input1 & filteredList (fun x => x % 2 == 1) %~ (· + 100)
  ensureEq "odd filter" [101, 2, 103, 4, 105, 6] result3

test "Filtered: edge cases" := do
  let evenFilter : Traversal' (List Nat) Nat := filteredList (fun x => x % 2 == 0)

  -- Empty list
  ensureEq "empty list" ([] : List Nat) (([] : List Nat) & evenFilter %~ (· * 100))

  -- No matches
  let odds : List Nat := [1, 3, 5, 7]
  ensureEq "no matches" odds (odds & evenFilter %~ (· * 100))

  -- All match
  let evens : List Nat := [2, 4, 6]
  ensureEq "all match" [200, 400, 600] (evens & evenFilter %~ (· * 100))

  -- Single element
  ensureEq "single match" [52] ([42] & evenFilter %~ (· + 10))
  ensureEq "single no match" [43] ([43] & evenFilter %~ (· + 10))

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
  | some result => ensureEq "successful validation" [1, 4, 3, 8, 5] result

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
  ensureEq "even indices" [10, 2, 30, 4, 50, 6] result1

  -- Modify odd indices only
  let result2 := [1, 2, 3, 4, 5, 6] & ifilteredList (fun i _ => i % 2 == 1) %~ (· + 100)
  ensureEq "odd indices" [1, 102, 3, 104, 5, 106] result2

  -- First 3 elements
  let result3 := [1, 2, 3, 4, 5, 6] & ifilteredList (fun i _ => i < 3) %~ (· * 10)
  ensureEq "first 3" [10, 20, 30, 4, 5, 6] result3

test "Indexed: focus single element with ix" := do
  let input : List Nat := [10, 20, 30, 40, 50]

  -- Modify element at index 3
  let result1 := input & ix 3 %~ (· * 10)
  ensureEq "ix modify" [10, 20, 30, 400, 50] result1

  -- Out of bounds (no-op)
  let result2 := input & ix 10 %~ (· * 999)
  ensureEq "ix out of bounds" input result2

  -- ix on empty
  let result3 := ([] : List Nat) & ix 0 %~ (· + 100)
  ensureEq "ix on empty" ([] : List Nat) result3

  -- Multiple ix operations
  let result4 := input
    |> (· & ix 0 %~ (· + 10))
    |> (· & ix 2 %~ (· + 20))
    |> (· & ix 4 %~ (· + 30))
  ensureEq "multiple ix" [20, 20, 50, 40, 80] result4

test "Indexed: optional access with atLens" := do
  let input : List Nat := [10, 20, 30, 40, 50]
  let at2 : Lens' (List Nat) (Option Nat) := atLens 2
  let at10 : Lens' (List Nat) (Option Nat) := atLens 10
  let at0 : Lens' (List Nat) (Option Nat) := atLens 0
  let at1 : Lens' (List Nat) (Option Nat) := atLens 1

  -- View at valid/invalid indices
  ensureEq "view at 2" (some 30) (input ^. at2)
  ensureEq "view out of bounds" (none : Option Nat) (input ^. at10)
  ensureEq "view empty" (none : Option Nat) (([] : List Nat) ^. at0)

  -- Set at valid index
  ensureEq "set at 2" [10, 20, 300, 40, 50] (input & at2 .~ some 300)

  -- Set out of bounds (no-op)
  ensureEq "set out of bounds" input (input & at10 .~ some 999)

  -- Over with Option.map
  let result : List Nat := input & at1 %~ Option.map (· * 10)
  ensureEq "over" [10, 200, 30, 40, 50] result

test "Combined: complex index+value predicates" := do
  let input : List Nat := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

  -- Even values at odd indices
  let result1 := input & ifilteredList (fun i v => i % 2 == 1 && v % 2 == 0) %~ (· * 100)
  ensureEq "even at odd" [1, 200, 3, 400, 5, 600, 7, 800, 9, 1000] result1

  -- Values greater than their index
  let input2 : List Nat := [0, 5, 1, 8, 2, 10, 3]
  let result2 := input2 & ifilteredList (fun i v => v > i) %~ (· * 2)
  ensureEq "value > index" [0, 10, 1, 16, 2, 20, 3] result2

  -- Value == index^2 (perfect squares)
  let squares : List Nat := [0, 1, 4, 9, 16, 25, 36]
  let result3 := squares & ifilteredList (fun i v => v == i * i) %~ (· + 1000)
  ensureEq "perfect squares" [1000, 1001, 1004, 1009, 1016, 1025, 1036] result3

test "Stateful: counting and accumulation" := do
  let input : List Nat := [1, 2, 3, 4, 5, 6]
  let evens : Traversal' (List Nat) Nat := filteredList (fun x => x % 2 == 0)

  -- Count matching elements
  let counter (x : Nat) : StateT Nat Id Nat := do
    let count ← get
    set (count + 1)
    pure x
  let (_, count) := (Traversal.traverse' evens counter input).run 0
  ensureEq "count evens" 3 count

  -- Accumulate sum
  let accumulator (x : Nat) : StateT Nat Id Nat := do
    let sum ← get
    set (sum + x)
    pure x
  let (_, sum) := (Traversal.traverse' evens accumulator input).run 0
  ensureEq "sum evens" 12 sum

  -- Running sum (using unfiltered list)
  let input2 : List Nat := [1, 2, 3, 4, 5]
  let tr : Traversal' (List Nat) Nat := Instances.List.traversed
  let runningSum (x : Nat) : StateT Nat Id Nat := do
    let s ← get
    let newSum := s + x
    set newSum
    pure newSum
  let (result, _) := (Traversal.traverse' tr runningSum input2).run 0
  ensureEq "running sum" [1, 3, 6, 10, 15] result

  -- Assign IDs only to filtered elements
  let input3 : List Nat := [1, 2, 3, 4, 5, 6, 7, 8]
  let idAssigner (_ : Nat) : StateT Nat Id Nat := do
    let id ← get
    set (id + 1)
    pure id
  let (result3, _) := (Traversal.traverse' evens idAssigner input3).run 100
  ensureEq "assign IDs" [1, 100, 3, 101, 5, 102, 7, 103] result3

test "Real-world: selective array updates" := do
  -- Increment at even positions
  let result1 := [1, 2, 3, 4, 5, 6, 7, 8] & ifilteredList (fun i _ => i % 2 == 0) %~ (· + 10)
  ensureEq "even positions" [11, 2, 13, 4, 15, 6, 17, 8] result1

  -- Zero out negatives
  let input2 : List Int := [-5, 10, -3, 0, 7, -2, 15]
  let result2 := input2 & filteredList (fun x : Int => x < 0) %~ (fun _ => 0)
  ensureEq "zero negatives" [0, 10, 0, 0, 7, 0, 15] result2

  -- Clamp large values
  let input3 : List Nat := [10, 150, 30, 200, 50, 180]
  let result3 := input3 & filteredList (fun x : Nat => x > 100) %~ (fun _ => 100)
  ensureEq "clamp large" [10, 100, 30, 100, 50, 100] result3

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
  ensureEq "double" [0, 10, 0, 0, 6, 0, 14, 0] (input & nonZero %~ (· * 2))

  -- Normalize to 1
  ensureEq "normalize" [0, 1, 0, 0, 1, 0, 1, 0] (input & nonZero %~ (fun _ => 1))

  -- Non-zero at even indices
  let input2 : List Nat := [0, 5, 10, 0, 20, 0, 30, 0]
  let result := input2 & ifilteredList (fun i v => v != 0 && i % 2 == 0) %~ (· + 1000)
  ensureEq "non-zero even idx" [0, 5, 1010, 0, 1020, 0, 1030, 0] result

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
  | some r => ensureEq "valid unchanged" valid r

  -- Combined filter
  let input : List Nat := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
  let evenLarge : Traversal' (List Nat) Nat := ifilteredList (fun _ v => v % 2 == 0 && v > 5)
  let result := input & evenLarge %~ (· * 10)
  ensureEq "fused filters" [1, 2, 3, 4, 5, 60, 7, 80, 9, 100] result

test "Composition: reusable and higher-order filters" := do
  let input : List Nat := [1, 2, 3, 4, 5, 6]

  -- Reusable evens filter with different transforms
  let evens : Traversal' (List Nat) Nat := filteredList (fun x => x % 2 == 0)
  ensureEq "evens * 2" [1, 4, 3, 8, 5, 12] (input & evens %~ (· * 2))
  ensureEq "evens + 100" [1, 102, 3, 104, 5, 106] (input & evens %~ (· + 100))

  -- Negated filter (NOT even = odd)
  let notEven : Traversal' (List Nat) Nat := filteredList (fun x => x % 2 != 0)
  ensureEq "negated filter" [11, 2, 13, 4, 15, 6] (input & notEven %~ (· + 10))

  -- Union: even OR > 4
  let union : Traversal' (List Nat) Nat := filteredList (fun x => x % 2 == 0 || x > 4)
  ensureEq "union" [1, 20, 3, 40, 50, 60] (input & union %~ (· * 10))

  -- Intersection: even AND > 3
  let intersection : Traversal' (List Nat) Nat := filteredList (fun x => x % 2 == 0 && x > 3)
  ensureEq "intersection" [1, 2, 3, 104, 5, 106] (input & intersection %~ (· + 100))

/-! ## String Optics Tests -/

test "String.chars: iso to List Char" := do
  let s := "hello"
  let charsIso : Iso' String (List Char) := chars
  let cs := s ^. charsIso
  ensureEq "chars forward" ['h', 'e', 'l', 'l', 'o'] cs
  let s' := review' charsIso ['w', 'o', 'r', 'l', 'd']
  ensureEq "chars backward" "world" s'

test "String.traversed: modify all characters" := do
  let s := "abc"
  let result := s & Collimator.Instances.String.traversed %~ Char.toUpper
  ensureEq "toUpper all" "ABC" result

test "String.traversed: collect characters" := do
  let s := "xyz"
  let cs := s ^.. Collimator.Instances.String.traversed
  ensureEq "collect chars" ['x', 'y', 'z'] cs

test "String.itraversed: indexed access" := do
  let s := "abc"
  let indexed := s ^.. Collimator.Instances.String.itraversed
  ensureEq "indexed chars" [(0, 'a'), (1, 'b'), (2, 'c')] indexed

test "String HasAt: valid index" := do
  let s := "hello"
  let c := s ^. atLens (ι := Nat) (s := String) (a := Char) 1
  ensureEq "char at 1" (some 'e') c

test "String HasAt: invalid index" := do
  let s := "hi"
  let c := s ^. atLens (ι := Nat) (s := String) (a := Char) 10
  ensureEq "char at 10" none c

test "String HasIx: modify at index" := do
  let s := "cat"
  let result := s & ix (ι := Nat) (s := String) (a := Char) 1 %~ (fun _ => 'o')
  ensureEq "modify char" "cot" result

test "String HasIx: out of bounds is no-op" := do
  let s := "dog"
  let result := s & ix (ι := Nat) (s := String) (a := Char) 100 %~ (fun _ => 'x')
  ensureEq "no-op" "dog" result

/-! ## Bifunctor Traversal Tests -/

test "both: traverse both components of pair" := do
  let pair := (3, 5)
  let result := pair & both %~ (· * 2)
  ensureEq "double both" (6, 10) result

test "both: collect both values" := do
  let pair := ("a", "b")
  let result := pair ^.. both
  ensureEq "collect both" ["a", "b"] result

test "both': monomorphic version" := do
  let pair := (10, 20)
  let result := pair & both' Int %~ (· + 1)
  ensureEq "both' increment" (11, 21) result

test "chosen: traverse left branch" := do
  let s : Sum Int Int := Sum.inl 42
  let result := s & chosen %~ (· * 2)
  ensureEq "double left" (Sum.inl 84) result

test "chosen: traverse right branch" := do
  let s : Sum Int Int := Sum.inr 99
  let result := s & chosen %~ (· + 1)
  ensureEq "increment right" (Sum.inr 100) result

test "chosen: collect from either branch" := do
  let left : Sum String String := Sum.inl "hello"
  let right : Sum String String := Sum.inr "world"
  let l := left ^.. chosen
  let r := right ^.. chosen
  ensureEq "left value" ["hello"] l
  ensureEq "right value" ["world"] r

test "chosen': monomorphic version" := do
  let s : Sum Int Int := Sum.inl 5
  let result := s & chosen' Int %~ (· * 10)
  ensureEq "chosen' scale" (Sum.inl 50) result

test "swapped: swap pair components" := do
  let pair := (1, 2)
  let swappedIso : Iso' (Int × Int) (Int × Int) := swapped
  let result := pair ^. swappedIso
  ensureEq "swapped" (2, 1) result

test "swappedSum: swap sum branches" := do
  let left : Sum Int Int := Sum.inl 42
  let right : Sum Int Int := Sum.inr 99
  let swappedSumIso : Iso' (Sum Int Int) (Sum Int Int) := swappedSum
  let l' := left ^. swappedSumIso
  let r' := right ^. swappedSumIso
  ensureEq "swap left" (Sum.inr 42) l'
  ensureEq "swap right" (Sum.inl 99) r'

test "beside: traverse both sides of pair" := do
  let pair := ([1, 2], [3, 4])
  let listTrav : Traversal' (List Int) Int := Collimator.Instances.List.traversed
  let t : Traversal' (List Int × List Int) Int := beside listTrav listTrav
  let result := pair & t %~ (· + 1)
  ensureEq "increment both lists" ([2, 3], [4, 5]) result

test "beside: collect from both sides" := do
  let pair := (["a", "b"], ["c"])
  let listTrav : Traversal' (List String) String := Collimator.Instances.List.traversed
  let t : Traversal' (List String × List String) String := beside listTrav listTrav
  let result := pair ^.. t
  ensureEq "collect all strings" ["a", "b", "c"] result

test "beside': monomorphic version" := do
  let pair := ([10, 20], [30])
  let listTrav : Traversal' (List Int) Int := Collimator.Instances.List.traversed
  let t : Traversal' (List Int × List Int) Int := beside' listTrav listTrav
  let result := pair & t %~ (· * 2)
  ensureEq "double all" ([20, 40], [60]) result

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
  ensureEq "traverse option and list" (some 15, [11, 12]) result

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
  ensureEq "list children" [[2, 3, 4]] cs

test "Plated List: overChildren" := do
  let xs := [1, 2, 3]
  -- Reverse the tail
  let result := overChildren List.reverse xs
  ensureEq "reverse tail" [1, 3, 2] result

test "Plated Option: no children" := do
  let x : Option Int := some 42
  let cs := childrenOf x
  ensureEq "option has no children" ([] : List (Option Int)) cs

test "Plated SimpleTree: children of node" := do
  let leaf1 := SimpleTree.leaf 1
  let leaf2 := SimpleTree.leaf 2
  let tree := SimpleTree.node leaf1 leaf2
  let cs := childrenOf tree
  ensureEq "tree children count" 2 cs.length

test "Plated SimpleTree: children of leaf" := do
  let leaf := SimpleTree.leaf 42
  let cs := childrenOf leaf
  ensureEq "leaf has no children" ([] : List SimpleTree) cs

test "transform: bottom-up transformation" := do
  let leaf1 := SimpleTree.leaf 1
  let leaf2 := SimpleTree.leaf 2
  let tree := SimpleTree.node leaf1 leaf2
  -- Double all leaf values
  let doubleLeaves : SimpleTree → SimpleTree
    | SimpleTree.leaf n => SimpleTree.leaf (n * 2)
    | t => t
  let result := transform doubleLeaves tree
  ensureEq "transform sum" 6 (sumLeaves result)  -- (1*2) + (2*2) = 6

test "universeList: collect all nodes" := do
  let leaf1 := SimpleTree.leaf 1
  let leaf2 := SimpleTree.leaf 2
  let tree := SimpleTree.node leaf1 leaf2
  let all := universeList tree
  -- Should include root + 2 leaves = 3 nodes
  ensureEq "universe count" 3 all.length

test "cosmosCount: count all nodes" := do
  let leaf1 := SimpleTree.leaf 1
  let leaf2 := SimpleTree.leaf 2
  let inner := SimpleTree.node leaf1 leaf2
  let tree := SimpleTree.node inner (SimpleTree.leaf 3)
  -- Tree structure: node(node(leaf, leaf), leaf) = 5 nodes
  ensureEq "cosmos count" 5 (cosmosCount tree)

test "depth: measure tree depth" := do
  let leaf := SimpleTree.leaf 1
  ensureEq "leaf depth" 1 (depth leaf)
  let shallow := SimpleTree.node leaf leaf
  ensureEq "shallow depth" 2 (depth shallow)
  let deep := SimpleTree.node shallow leaf
  ensureEq "deep depth" 3 (depth deep)

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
  ensureEq "rewrite result" (SimpleTree.leaf 1) result

#generate_tests

end CollimatorTests.CombinatorTests
