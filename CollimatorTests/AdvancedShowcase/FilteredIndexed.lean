import CollimatorTests.Framework
import Collimator.Prelude
import Collimator.Helpers

/-!
# Filtered & Indexed Combinations

Demonstrate advanced traversal combinators:
- `filteredList`: Focus only on elements matching a predicate
- `ifilteredList`: Access both index and value during traversal
- Combining filters and indexes for complex queries
- Effectful and stateful traversals
-/

open CollimatorTests
open Collimator
open Collimator.Combinators (filteredList ifilteredList)
open Collimator.Indexed
open Collimator.Instances.List
open Collimator.Instances.Option
open scoped Collimator.Operators

namespace CollimatorTests.AdvancedShowcase.FilteredIndexed

testSuite "Filtered & Indexed"

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

/-! ## Filtered Operations -/


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

    IO.println "✓ Filtered basics tests passed"


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

    IO.println "✓ Filtered edge cases tests passed"


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

    IO.println "✓ Filtered effectful tests passed"


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

    IO.println "✓ Filtered with lens composition tests passed"

/-! ## Indexed Operations -/


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

    IO.println "✓ Indexed basics tests passed"


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

    IO.println "✓ Indexed ix tests passed"


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

    IO.println "✓ Indexed atLens tests passed"

/-! ## Combined Filtered + Indexed -/


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

    IO.println "✓ Filtered indexed complex tests passed"

/-! ## Stateful Operations -/


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

    IO.println "✓ Stateful tests passed"

/-! ## Real-World Use Cases -/


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

    IO.println "✓ Real-world array updates tests passed"


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

    IO.println "✓ Real-world conditional batch tests passed"


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

    IO.println "✓ Real-world sparse arrays tests passed"

/-! ## Performance Patterns -/

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

    IO.println "✓ Performance tests passed"

/-! ## Composition Patterns -/

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

    IO.println "✓ Composition tests passed"

#generate_tests

end CollimatorTests.AdvancedShowcase.FilteredIndexed
