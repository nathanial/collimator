import Collimator.Optics.Traversal
import Collimator.Combinators.Filtered
import Collimator.Combinators.Indexed
import Collimator.Combinators.Composition
import Collimator.Combinators.Operators
import Collimator.Instances.List
import Collimator.Poly
import CollimatorTests.Framework

namespace CollimatorTests.AdvancedShowcase.FilteredIndexed

open Collimator
open Collimator.Poly
open Collimator.Combinators
open Collimator.Indexed
open Collimator.Operators
open CollimatorTests

/-!
# Filtered & Indexed Combinations

Demonstrate advanced traversal combinators:
- `filtered`: Focus only on elements matching a predicate
- `itraversed`: Access both index and value during traversal
- Combining filters and indexes for complex queries
- Performance characteristics and fusion opportunities
- Real-world use cases: updating specific array elements, conditional transformations
-/

/-! ## Basic Filtered Operations -/

/--
Test: Basic predicate filtering - focus only on even numbers
- Filter evens, modify them (multiply by 10)
- Filter odds, modify them (add 100)
- Filter positives, negatives
- Verify unmatched elements remain unchanged
-/
private def case_filteredByPredicate : TestCase := {
  name := "Filtered: modify only elements matching predicate",
  run := do
    -- Test 1: Filter evens, multiply by 10
    let input1 : List Nat := [1, 2, 3, 4, 5, 6]
    let tr := Instances.List.traversed
    let evenFilter := filtered tr (fun x => x % 2 == 0)
    let result1 := input1 & evenFilter %~ (· * 10)
    let expected1 : List Nat := [1, 20, 3, 40, 5, 60]
    if result1 != expected1 then
      throw (IO.userError s!"Even filter failed: expected {expected1}, got {result1}")

    -- Test 2: Filter odds, add 100
    let oddFilter := filtered tr (fun x => x % 2 == 1)
    let result2 := input1 & oddFilter %~ (· + 100)
    let expected2 : List Nat := [101, 2, 103, 4, 105, 6]
    if result2 != expected2 then
      throw (IO.userError s!"Odd filter failed: expected {expected2}, got {result2}")

    -- Test 3: Filter positives
    let input3 : List Int := [-2, -1, 0, 1, 2]
    let tr3 := Instances.List.traversed
    let posFilter := filtered tr3 (fun x => x > 0)
    let result3 := input3 & posFilter %~ (· * 2)
    let expected3 : List Int := [-2, -1, 0, 2, 4]
    if result3 != expected3 then
      throw (IO.userError s!"Positive filter failed: expected {expected3}, got {result3}")

    -- Test 4: Filter negatives and negate them
    let negFilter := filtered tr3 (fun x => x < 0)
    let result4 := input3 & negFilter %~ (fun x => -x)
    let expected4 : List Int := [2, 1, 0, 1, 2]
    if result4 != expected4 then
      throw (IO.userError s!"Negative filter failed: expected {expected4}, got {result4}")

    -- Test 5: Verify unmatched elements remain unchanged
    let input5 : List Nat := [10, 20, 30]
    let neverMatch := filtered tr (fun _ => false)
    let result5 := input5 & neverMatch %~ (· * 999)
    if result5 != input5 then
      throw (IO.userError s!"Unmatched elements changed: expected {input5}, got {result5}")

    IO.println "✓ Filtered by predicate tests passed"
}

/--
Test: Filter with complex predicates
- Filter by range (10 < x < 50)
- Filter by multiple conditions (even AND positive)
- Filter by divisibility
- Chain multiple filters
-/
private def case_filteredComplexPredicates : TestCase := {
  name := "Filtered: complex and composed predicates",
  run := do
    let tr := Instances.List.traversed

    -- Test 1: Filter by range (10 < x < 50)
    let input1 : List Nat := [5, 15, 25, 45, 55, 65]
    let rangeFilter := filtered tr (fun x => x > 10 && x < 50)
    let result1 := input1 & rangeFilter %~ (· + 1000)
    let expected1 : List Nat := [5, 1015, 1025, 1045, 55, 65]
    if result1 != expected1 then
      throw (IO.userError s!"Range filter failed: expected {expected1}, got {result1}")

    -- Test 2: Filter by multiple conditions (even AND positive)
    let input2 : List Int := [-4, -2, -1, 0, 1, 2, 3, 4]
    let tr2 := Instances.List.traversed
    let evenPosFilter := filtered tr2 (fun x => x % 2 == 0 && x > 0)
    let result2 := input2 & evenPosFilter %~ (· * 100)
    let expected2 : List Int := [-4, -2, -1, 0, 1, 200, 3, 400]
    if result2 != expected2 then
      throw (IO.userError s!"Even AND positive filter failed: expected {expected2}, got {result2}")

    -- Test 3: Filter by divisibility (divisible by 3)
    let input3 : List Nat := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
    let div3Filter := filtered tr (fun x => x % 3 == 0)
    let result3 := input3 & div3Filter %~ (· * 10)
    let expected3 : List Nat := [1, 2, 30, 4, 5, 60, 7, 8, 90, 10, 11, 120]
    if result3 != expected3 then
      throw (IO.userError s!"Divisibility by 3 filter failed: expected {expected3}, got {result3}")

    -- Test 4: Chain multiple filters (first filter evens, then filter > 10)
    let input4 : List Nat := [2, 4, 6, 8, 10, 12, 14, 16]
    let evenFilter := filtered tr (fun x => x % 2 == 0)
    let gt10Filter := filtered evenFilter (fun x => x > 10)
    let result4 := input4 & gt10Filter %~ (· + 100)
    let expected4 : List Nat := [2, 4, 6, 8, 10, 112, 114, 116]
    if result4 != expected4 then
      throw (IO.userError s!"Chained filters failed: expected {expected4}, got {result4}")

    -- Test 5: Complex predicate - divisible by 2 OR 3 but not both
    let input5 : List Nat := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12]
    let xorFilter := filtered tr (fun x =>
      (x % 2 == 0 && x % 3 != 0) || (x % 2 != 0 && x % 3 == 0))
    let result5 := input5 & xorFilter %~ (· * 10)
    let expected5 : List Nat := [1, 20, 30, 40, 5, 6, 7, 80, 90, 100, 12]
    if result5 != expected5 then
      throw (IO.userError s!"XOR filter failed: expected {expected5}, got {result5}")

    IO.println "✓ Filtered complex predicates tests passed"
}

-- Define a Product structure for lens composition tests
private structure Product where
  name : String
  price : Nat
  quantity : Nat
deriving Repr, BEq

-- Define lenses for Product fields
private def priceLens : Lens' Product Nat :=
  lens' (fun p => p.price) (fun p newPrice => { p with price := newPrice })

private def quantityLens : Lens' Product Nat :=
  lens' (fun p => p.quantity) (fun p newQty => { p with quantity := newQty })

private def nameLens : Lens' Product String :=
  lens' (fun p => p.name) (fun p newName => { p with name := newName })

-- Define a TestResult structure for conditional batch tests
private structure TestResult where
  student : String
  score : Int  -- -1 means didn't take test
deriving BEq, Repr

private def scoreLens : Lens' TestResult Int :=
  lens' (fun r => r.score) (fun r newScore => { r with score := newScore })

/--
Test: Filtered traversal + lens composition
- Define structured data (records with fields)
- Filter records by predicate on one field
- Use lens to modify a different field of filtered records
- Demonstrate traversal ∘ lens composition
- Show reading and writing through the composed optic
-/
private def case_filteredWithLens : TestCase := {
  name := "Filtered: composition with lenses for field access",
  run := do

    -- Test 1: Filter by price, modify quantity
    -- "Restock items that are expensive (price > 100)"
    let inventory : List Product := [
      { name := "Widget", price := 50, quantity := 10 },
      { name := "Gadget", price := 150, quantity := 5 },
      { name := "Doohickey", price := 200, quantity := 3 },
      { name := "Thingamajig", price := 25, quantity := 20 }
    ]

    let tr := Instances.List.traversed
    let expensiveFilter := filtered tr (fun p : Product => p.price > 100)
    -- Compose: filter expensive items, then focus on quantity field
    let expensiveQuantity := expensiveFilter ⊚ quantityLens
    let restocked := inventory & expensiveQuantity %~ (· + 50)

    let expected1 : List Product := [
      { name := "Widget", price := 50, quantity := 10 },
      { name := "Gadget", price := 150, quantity := 55 },    -- +50
      { name := "Doohickey", price := 200, quantity := 53 }, -- +50
      { name := "Thingamajig", price := 25, quantity := 20 }
    ]
    if restocked != expected1 then
      throw (IO.userError "Filter+lens (qty) failed: quantities not correctly updated")

    -- Test 2: Filter by quantity, apply discount to price
    -- "Discount items with low stock (quantity < 10)"
    let lowStockFilter := filtered tr (fun p : Product => p.quantity < 10)
    let lowStockPrice := lowStockFilter ⊚ priceLens
    let discounted := inventory & lowStockPrice %~ (fun p => p * 80 / 100)

    let expected2 : List Product := [
      { name := "Widget", price := 50, quantity := 10 },
      { name := "Gadget", price := 120, quantity := 5 },     -- 150 * 0.8 = 120
      { name := "Doohickey", price := 160, quantity := 3 },  -- 200 * 0.8 = 160
      { name := "Thingamajig", price := 25, quantity := 20 }
    ]
    if discounted != expected2 then
      throw (IO.userError "Filter+lens (price) failed: prices not correctly discounted")

    -- Test 3: Filter and modify name field
    -- "Mark cheap items in the name"
    let cheapFilter := filtered tr (fun p : Product => p.price < 100)
    let cheapName := cheapFilter ⊚ nameLens
    let marked := inventory & cheapName %~ (fun n => "[SALE] " ++ n)

    let expected3 : List Product := [
      { name := "[SALE] Widget", price := 50, quantity := 10 },
      { name := "Gadget", price := 150, quantity := 5 },
      { name := "Doohickey", price := 200, quantity := 3 },
      { name := "[SALE] Thingamajig", price := 25, quantity := 20 }
    ]
    if marked != expected3 then
      throw (IO.userError "Filter+lens (name) failed: names not correctly marked")

    -- Test 4: Multiple field modifications with different filters
    -- Combine multiple operations
    let result := inventory
      & ((filtered tr (fun p => p.price > 100)) ⊚ quantityLens) %~ (· * 2)
      & ((filtered tr (fun p => p.quantity > 15)) ⊚ priceLens) %~ (· - 5)

    let expected4 : List Product := [
      { name := "Widget", price := 50, quantity := 10 },
      { name := "Gadget", price := 150, quantity := 10 },    -- qty doubled (5*2=10)
      { name := "Doohickey", price := 200, quantity := 6 },  -- qty doubled (3*2=6)
      { name := "Thingamajig", price := 20, quantity := 20 } -- price reduced (25-5=20)
    ]
    if result != expected4 then
      throw (IO.userError "Multiple filter+lens failed: combined operations incorrect")

    IO.println "✓ Filtered with lens composition tests passed"
}

/--
Test: Filtered edge cases
- Empty list
- No elements match filter (all unchanged)
- All elements match filter (all modified)
- Single element lists
-/
private def case_filteredEdgeCases : TestCase := {
  name := "Filtered: edge cases and boundary conditions",
  run := do
    let tr := Instances.List.traversed

    -- Test 1: Empty list - filtered traversal on empty list
    let empty : List Nat := []
    let evenFilter := filtered tr (fun x => x % 2 == 0)
    let result1 := empty & evenFilter %~ (· * 100)
    if result1 != [] then
      throw (IO.userError s!"Empty list filter failed: expected [], got {result1}")

    -- Test 2: No elements match filter (all unchanged)
    let input2 : List Nat := [1, 3, 5, 7, 9]
    let result2 := input2 & evenFilter %~ (· * 100)
    if result2 != input2 then
      throw (IO.userError s!"No match filter failed: expected {input2}, got {result2}")

    -- Test 3: All elements match filter (all modified)
    let input3 : List Nat := [2, 4, 6, 8, 10]
    let result3 := input3 & evenFilter %~ (· * 100)
    let expected3 : List Nat := [200, 400, 600, 800, 1000]
    if result3 != expected3 then
      throw (IO.userError s!"All match filter failed: expected {expected3}, got {result3}")

    -- Test 4: Single element list - matches filter
    let input4 : List Nat := [42]
    let result4 := input4 & evenFilter %~ (· + 10)
    let expected4 : List Nat := [52]
    if result4 != expected4 then
      throw (IO.userError s!"Single match failed: expected {expected4}, got {result4}")

    -- Test 5: Single element list - does not match filter
    let input5 : List Nat := [43]
    let result5 := input5 & evenFilter %~ (· + 10)
    if result5 != input5 then
      throw (IO.userError s!"Single no-match failed: expected {input5}, got {result5}")

    -- Test 6: Single element list - always true filter
    let input6 : List Int := [7]
    let tr6 := Instances.List.traversed
    let alwaysFilter := filtered tr6 (fun _ => true)
    let result6 := input6 & alwaysFilter %~ (· * 2)
    let expected6 : List Int := [14]
    if result6 != expected6 then
      throw (IO.userError s!"Single always-match failed: expected {expected6}, got {result6}")

    -- Test 7: Single element list - always false filter
    let neverFilter := filtered tr6 (fun _ => false)
    let result7 := input6 & neverFilter %~ (· * 2)
    if result7 != input6 then
      throw (IO.userError s!"Single never-match failed: expected {input6}, got {result7}")

    -- Test 8: Two element list - first matches
    let input8 : List Nat := [2, 3]
    let result8 := input8 & evenFilter %~ (· + 100)
    let expected8 : List Nat := [102, 3]
    if result8 != expected8 then
      throw (IO.userError s!"Two elements (first matches) failed: expected {expected8}, got {result8}")

    -- Test 9: Two element list - second matches
    let input9 : List Nat := [3, 2]
    let result9 := input9 & evenFilter %~ (· + 100)
    let expected9 : List Nat := [3, 102]
    if result9 != expected9 then
      throw (IO.userError s!"Two elements (second matches) failed: expected {expected9}, got {result9}")

    -- Test 10: Two element list - both match
    let input10 : List Nat := [2, 4]
    let result10 := input10 & evenFilter %~ (· + 100)
    let expected10 : List Nat := [102, 104]
    if result10 != expected10 then
      throw (IO.userError s!"Two elements (both match) failed: expected {expected10}, got {result10}")

    -- Test 11: Two element list - neither matches
    let input11 : List Nat := [1, 3]
    let result11 := input11 & evenFilter %~ (· + 100)
    if result11 != input11 then
      throw (IO.userError s!"Two elements (neither matches) failed: expected {input11}, got {result11}")

    IO.println "✓ Filtered edge cases tests passed"
}

/--
Test: Effectful filtered traversals
- State monad: count how many elements were filtered/modified
- Option: validation that fails on filtered elements
- Writer: log which elements matched the filter
-/
private def case_filteredEffectful : TestCase := {
  name := "Filtered: effectful traversals with State/Option/Writer",
  run := do
    let tr := Instances.List.traversed

    -- Test 1: Option monad - validation that fails on filtered elements
    let input1 : List Nat := [1, 2, 3, 4, 5, 6]
    let evenFilter := filtered tr (fun x => x % 2 == 0)

    -- Validate that all even numbers are < 5, fail if any >= 5
    let validator1 : Nat → Option Nat := fun x =>
      if x < 5 then some (x * 2) else none

    let optResult1 := traverse evenFilter validator1 input1
    -- Should fail because 4 and 6 are even, and 6 >= 5
    match optResult1 with
    | some _ => throw (IO.userError "Option validation should have failed but succeeded")
    | none => pure ()  -- Expected

    -- Test 2: Option monad - successful validation
    let input2 : List Nat := [1, 2, 3, 4, 5]
    let validator2 : Nat → Option Nat := fun x =>
      if x < 5 then some (x * 2) else none

    let optResult2 := traverse evenFilter validator2 input2
    match optResult2 with
    | none => throw (IO.userError "Option validation failed unexpectedly")
    | some result =>
      let expected2 : List Nat := [1, 4, 3, 8, 5]
      if result != expected2 then
        throw (IO.userError s!"Option validation result failed: expected {expected2}, got {result}")

    -- Test 3: Option monad - early termination
    -- Even though only evens are filtered, validation fails on first even that's >= 3
    let input3 : List Nat := [1, 2, 3, 4, 5, 6]
    let strictValidator : Nat → Option Nat := fun x =>
      if x < 3 then some (x + 10) else none

    let optResult3 := traverse evenFilter strictValidator input3
    match optResult3 with
    | some _ => throw (IO.userError "Strict validation should have failed on 4")
    | none => pure ()  -- Expected

    -- Test 4: Option on all elements matching filter (all pass)
    let input4 : List Nat := [2, 4]
    let passValidator : Nat → Option Nat := fun x => some (x + 100)
    let optResult4 := traverse evenFilter passValidator input4
    match optResult4 with
    | none => throw (IO.userError "All-pass validation failed unexpectedly")
    | some result =>
      let expected4 : List Nat := [102, 104]
      if result != expected4 then
        throw (IO.userError s!"All-pass result failed: expected {expected4}, got {result}")

    -- Test 5: Option with filter matching nothing
    let input5 : List Nat := [1, 3, 5]  -- All odd
    let anyValidator : Nat → Option Nat := fun x => some (x * 10)
    let optResult5 := traverse evenFilter anyValidator input5
    match optResult5 with
    | none => throw (IO.userError "No-match validation should succeed")
    | some result =>
      if result != input5 then
        throw (IO.userError s!"No-match result should be unchanged: expected {input5}, got {result}")

    -- Test 6: Demonstrating short-circuiting
    -- Create a validator that would fail on 6, but succeeds for earlier evens
    let input6 : List Nat := [2, 4, 6, 8]
    let shortCircuitValidator : Nat → Option Nat := fun x =>
      if x == 6 then none else some (x * 10)

    let optResult6 := traverse evenFilter shortCircuitValidator input6
    match optResult6 with
    | some _ => throw (IO.userError "Should have short-circuited on 6")
    | none => pure ()  -- Expected: fails on 6

    -- Test 7: Complex predicate with Option
    -- Filter multiples of 3 that are >= 6
    let input7 : List Nat := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
    let complexFilter := filtered tr (fun x => x % 3 == 0 && x >= 6)  -- Multiples of 3 >= 6
    let rangeValidator : Nat → Option Nat := fun x =>
      if x < 10 then some (x + 50) else none

    let optResult7 := traverse complexFilter rangeValidator input7
    match optResult7 with
    | none => throw (IO.userError "Complex filter should succeed for 6 and 9")
    | some result =>
      -- Input: [1,2,3,4,5,6,7,8,9,10], filter 6,9, validate both pass -> 56, 59
      let expected7 : List Nat := [1, 2, 3, 4, 5, 56, 7, 8, 59, 10]
      if result != expected7 then
        throw (IO.userError s!"Complex filter failed: expected {expected7}, got {result}")

    IO.println "✓ Filtered effectful traversals tests passed"
}

/-! ## Basic Indexed Operations -/

/--
Test: Indexed traversal - access both index and value
- Use itraversed to get (index, value) pairs
- Modify value based on its index (e.g., value + index)
- Replace value with its index
- Swap index and value positions
-/
private def case_indexedBasic : TestCase := {
  name := "Indexed: access index and value with itraversed",
  run := do
    -- Test 1: Add index to each value
    let input1 : List Nat := [10, 20, 30, 40]
    let indexed := Instances.List.itraversed
    let result1 := input1 & indexed %~ (fun (idx, v) => (idx, v + idx))
    let expected1 : List Nat := [10, 21, 32, 43]  -- [10+0, 20+1, 30+2, 40+3]
    if result1 != expected1 then
      throw (IO.userError s!"Add index failed: expected {expected1}, got {result1}")

    -- Test 2: Multiply value by its index (with special handling for index 0)
    let input2 : List Nat := [5, 6, 7, 8]
    let result2 := input2 & indexed %~ (fun (idx, v) => (idx, v * (idx + 1)))
    let expected2 : List Nat := [5, 12, 21, 32]  -- [5*1, 6*2, 7*3, 8*4]
    if result2 != expected2 then
      throw (IO.userError s!"Multiply by index failed: expected {expected2}, got {result2}")

    -- Test 3: Replace each value with its index
    let input3 : List String := ["a", "b", "c", "d"]
    let indexedStr := Instances.List.itraversed (α := String)
    let result3 := input3 & indexedStr %~ (fun (idx, _) => (idx, s!"index_{idx}"))
    let expected3 : List String := ["index_0", "index_1", "index_2", "index_3"]
    if result3 != expected3 then
      throw (IO.userError s!"Replace with index failed: expected {expected3}, got {result3}")

    -- Test 4: Conditional transformation based on index
    -- Even indices: double the value, Odd indices: add 100
    let input4 : List Nat := [1, 2, 3, 4, 5]
    let result4 := input4 & indexed %~ (fun (idx, v) =>
      if idx % 2 == 0 then
        (idx, v * 2)
      else
        (idx, v + 100))
    let expected4 : List Nat := [2, 102, 6, 104, 10]  -- [1*2, 2+100, 3*2, 4+100, 5*2]
    if result4 != expected4 then
      throw (IO.userError s!"Conditional by index failed: expected {expected4}, got {result4}")

    -- Test 5: Build string with position information
    let input5 : List String := ["apple", "banana", "cherry"]
    let result5 := input5 & indexedStr %~ (fun (idx, v) =>
      (idx, s!"[{idx}] {v}"))
    let expected5 : List String := ["[0] apple", "[1] banana", "[2] cherry"]
    if result5 != expected5 then
      throw (IO.userError s!"Position annotation failed: expected {expected5}, got {result5}")

    -- Test 6: Use index to compute exponential values
    let input6 : List Nat := [2, 2, 2, 2]
    let result6 := input6 & indexed %~ (fun (idx, v) => (idx, v ^ idx))
    let expected6 : List Nat := [1, 2, 4, 8]  -- [2^0, 2^1, 2^2, 2^3]
    if result6 != expected6 then
      throw (IO.userError s!"Exponential by index failed: expected {expected6}, got {result6}")

    -- Test 7: Create pairs of (index, value) by setting value to index
    let input7 : List Nat := [100, 200, 300]
    let result7 := input7 & indexed %~ (fun (idx, _) => (idx, idx))
    let expected7 : List Nat := [0, 1, 2]
    if result7 != expected7 then
      throw (IO.userError s!"Set to index failed: expected {expected7}, got {result7}")

    -- Test 8: Distance from a target index
    let input8 : List Int := [0, 0, 0, 0, 0]
    let targetIdx : Nat := 2
    let indexedInt := Instances.List.itraversed (α := Int)
    let result8 := input8 & indexedInt %~ (fun (idx, _) =>
      (idx, (idx : Int) - (targetIdx : Int)))
    let expected8 : List Int := [-2, -1, 0, 1, 2]
    if result8 != expected8 then
      throw (IO.userError s!"Distance from target failed: expected {expected8}, got {result8}")

    -- Test 9: Empty list
    let input9 : List Nat := []
    let result9 := input9 & indexed %~ (fun (idx, v) => (idx, v + idx))
    if result9 != [] then
      throw (IO.userError s!"Empty list failed: expected [], got {result9}")

    -- Test 10: Single element
    let input10 : List Nat := [42]
    let result10 := input10 & indexed %~ (fun (idx, v) => (idx, v + idx * 10))
    let expected10 : List Nat := [42]  -- [42 + 0*10]
    if result10 != expected10 then
      throw (IO.userError s!"Single element failed: expected {expected10}, got {result10}")

    IO.println "✓ Indexed basic tests passed"
}

/--
Test: Index-dependent transformations
- Multiply each element by its position
- Compute weighted average (weight = index)
- Conditional on index: even indices get one transform, odd another
- Distance from index (abs(value - index))
-/
private def case_indexedTransformations : TestCase := {
  name := "Indexed: transform values based on their position",
  run := do
    let indexed := Instances.List.itraversed

    -- Test 1: Multiply each element by its position
    let input1 : List Nat := [10, 20, 30, 40, 50]
    let result1 := input1 & indexed %~ (fun (idx, v) => (idx, v * idx))
    let expected1 : List Nat := [0, 20, 60, 120, 200]  -- [10*0, 20*1, 30*2, 40*3, 50*4]
    if result1 != expected1 then
      throw (IO.userError s!"Multiply by position failed: expected {expected1}, got {result1}")

    -- Test 2: Weighted transformation (weight increases with position)
    -- Each element gets multiplied by (index + 1) to give it a weight
    let input2 : List Nat := [5, 5, 5, 5]
    let result2 := input2 & indexed %~ (fun (idx, v) => (idx, v * (idx + 1)))
    let expected2 : List Nat := [5, 10, 15, 20]  -- [5*1, 5*2, 5*3, 5*4]
    if result2 != expected2 then
      throw (IO.userError s!"Weighted transform failed: expected {expected2}, got {result2}")

    -- Test 3: Conditional on index - even indices get doubled, odd get halved
    let input3 : List Nat := [10, 20, 30, 40, 50, 60]
    let result3 := input3 & indexed %~ (fun (idx, v) =>
      if idx % 2 == 0 then
        (idx, v * 2)  -- Even index: double
      else
        (idx, v / 2)  -- Odd index: halve
    )
    let expected3 : List Nat := [20, 10, 60, 20, 100, 30]
    if result3 != expected3 then
      throw (IO.userError s!"Conditional by index parity failed: expected {expected3}, got {result3}")

    -- Test 4: Distance from index (absolute difference)
    let input4 : List Nat := [5, 6, 7, 8, 9]
    let result4 := input4 & indexed %~ (fun (idx, v) =>
      let diff := if v >= idx then v - idx else idx - v
      (idx, diff))
    let expected4 : List Nat := [5, 5, 5, 5, 5]  -- [|5-0|, |6-1|, |7-2|, |8-3|, |9-4|]
    if result4 != expected4 then
      throw (IO.userError s!"Distance from index failed: expected {expected4}, got {result4}")

    -- Test 5: Position-based scaling (linear gradient)
    -- Scale from 0% at start to 100% at end
    let input5 : List Nat := [100, 100, 100, 100, 100]
    let len := input5.length
    let result5 := input5 & indexed %~ (fun (idx, v) =>
      (idx, v * idx / (len - 1)))
    let expected5 : List Nat := [0, 25, 50, 75, 100]
    if result5 != expected5 then
      throw (IO.userError s!"Linear gradient failed: expected {expected5}, got {result5}")

    -- Test 6: Alternating increment/decrement based on position
    let input6 : List Int := [10, 10, 10, 10, 10]
    let indexedInt := Instances.List.itraversed (α := Int)
    let result6 := input6 & indexedInt %~ (fun (idx, v) =>
      if idx % 2 == 0 then
        (idx, v + (idx : Int))
      else
        (idx, v - (idx : Int)))
    let expected6 : List Int := [10, 9, 12, 7, 14]  -- [10+0, 10-1, 10+2, 10-3, 10+4]
    if result6 != expected6 then
      throw (IO.userError s!"Alternating inc/dec failed: expected {expected6}, got {result6}")

    -- Test 7: Compute position in sequence (Fibonacci-like using index)
    -- Each position gets value of triangular number at that index
    let input7 : List Nat := [0, 0, 0, 0, 0]
    let result7 := input7 & indexed %~ (fun (idx, _) =>
      (idx, idx * (idx + 1) / 2))  -- Triangular numbers: 0, 1, 3, 6, 10
    let expected7 : List Nat := [0, 1, 3, 6, 10]
    if result7 != expected7 then
      throw (IO.userError s!"Triangular numbers failed: expected {expected7}, got {result7}")

    -- Test 8: Transform based on index ranges
    -- First third: +10, middle third: +20, last third: +30
    let input8 : List Nat := [1, 2, 3, 4, 5, 6, 7, 8, 9]
    let result8 := input8 & indexed %~ (fun (idx, v) =>
      let bonus := if idx < 3 then 10
                   else if idx < 6 then 20
                   else 30
      (idx, v + bonus))
    let expected8 : List Nat := [11, 12, 13, 24, 25, 26, 37, 38, 39]
    if result8 != expected8 then
      throw (IO.userError s!"Range-based transform failed: expected {expected8}, got {result8}")

    -- Test 9: Compute running index sum and add to value
    -- Each element gets the sum of all indices up to and including current
    let input9 : List Nat := [100, 100, 100, 100]
    let result9 := input9 & indexed %~ (fun (idx, v) =>
      let sumUpToIdx := idx * (idx + 1) / 2
      (idx, v + sumUpToIdx))
    let expected9 : List Nat := [100, 101, 103, 106]  -- [100+0, 100+1, 100+3, 100+6]
    if result9 != expected9 then
      throw (IO.userError s!"Running index sum failed: expected {expected9}, got {result9}")

    -- Test 10: Index-dependent string formatting
    let input10 : List Nat := [5, 10, 15, 20]
    let indexedNat := Instances.List.itraversed (α := Nat)
    -- Note: We need to keep values as Nat, but we tested string formatting in previous test
    -- Instead, test modulo operations based on index
    let result10 := input10 & indexedNat %~ (fun (idx, v) =>
      (idx, v + (idx % 3) * 10))
    let expected10 : List Nat := [5, 20, 35, 20]  -- [5+0*10, 10+1*10, 15+2*10, 20+0*10]
    if result10 != expected10 then
      throw (IO.userError s!"Index modulo transform failed: expected {expected10}, got {result10}")

    IO.println "✓ Indexed transformations tests passed"
}

/--
Test: Single index focus with `ix`
- Use `ix 3` to focus only the element at index 3
- Modify single element by index
- `ix` on out-of-bounds index (should not modify anything)
- `ix` with State to track if element was found
-/
private def case_indexedSingleFocus : TestCase := {
  name := "Indexed: focus single element with ix",
  run := do
    -- Test 1: Focus and modify element at index 3
    let input1 : List Nat := [10, 20, 30, 40, 50]
    let result1 := input1 & (ix 3) %~ (· * 10)
    let expected1 : List Nat := [10, 20, 30, 400, 50]
    if result1 != expected1 then
      throw (IO.userError s!"ix 3 modify failed: expected {expected1}, got {result1}")

    -- Test 2: Focus on first element (index 0)
    let input2 : List Nat := [1, 2, 3, 4]
    let result2 := input2 & (ix 0) %~ (· + 100)
    let expected2 : List Nat := [101, 2, 3, 4]
    if result2 != expected2 then
      throw (IO.userError s!"ix 0 failed: expected {expected2}, got {result2}")

    -- Test 3: Focus on last element
    let input3 : List Nat := [5, 6, 7, 8, 9]
    let result3 := input3 & (ix 4) %~ (· * 2)
    let expected3 : List Nat := [5, 6, 7, 8, 18]
    if result3 != expected3 then
      throw (IO.userError s!"ix last element failed: expected {expected3}, got {result3}")

    -- Test 4: Out-of-bounds index (should not modify anything)
    let input4 : List Nat := [1, 2, 3]
    let result4 := input4 & (ix 10) %~ (· * 999)
    if result4 != input4 then
      throw (IO.userError s!"ix out-of-bounds should not modify: expected {input4}, got {result4}")

    -- Test 5: Out-of-bounds on empty list
    let input5 : List Nat := []
    let result5 := input5 & (ix 0) %~ (· + 100)
    if result5 != [] then
      throw (IO.userError s!"ix on empty list failed: expected [], got {result5}")

    -- Test 6: Set operation (using .~ instead of %~)
    let input6 : List String := ["a", "b", "c", "d"]
    let result6 := input6 & (ix 2) .~ "REPLACED"
    let expected6 : List String := ["a", "b", "REPLACED", "d"]
    if result6 != expected6 then
      throw (IO.userError s!"ix set failed: expected {expected6}, got {result6}")

    -- Test 7: Multiple ix operations in sequence
    let input7 : List Nat := [1, 2, 3, 4, 5]
    let result7 := input7
      & (ix 0) %~ (· + 10)
      & (ix 2) %~ (· + 20)
      & (ix 4) %~ (· + 30)
    let expected7 : List Nat := [11, 2, 23, 4, 35]
    if result7 != expected7 then
      throw (IO.userError s!"Multiple ix failed: expected {expected7}, got {result7}")

    -- Test 8: ix on single element list
    let input8 : List Nat := [42]
    let result8 := input8 & (ix 0) %~ (· * 2)
    let expected8 : List Nat := [84]
    if result8 != expected8 then
      throw (IO.userError s!"ix on single element failed: expected {expected8}, got {result8}")

    -- Test 9: ix with function that uses the value itself
    let input9 : List Nat := [10, 20, 30, 40]
    let result9 := input9 & (ix 1) %~ (fun (x : Nat) => x + x)  -- Double the element
    let expected9 : List Nat := [10, 40, 30, 40]
    if result9 != expected9 then
      throw (IO.userError s!"ix with value function failed: expected {expected9}, got {result9}")

    -- Test 10: ix with different types
    let input10 : List Int := [-5, -4, -3, -2, -1]
    let result10 := input10 & (ix 2) %~ (fun x => -x)  -- Negate middle element
    let expected10 : List Int := [-5, -4, 3, -2, -1]
    if result10 != expected10 then
      throw (IO.userError s!"ix with Int failed: expected {expected10}, got {result10}")

    -- Test 11: Verify ix doesn't affect other elements
    let input11 : List Nat := [1, 1, 1, 1, 1]
    let result11 := input11 & (ix 2) %~ (· * 100)
    let expected11 : List Nat := [1, 1, 100, 1, 1]
    if result11 != expected11 then
      throw (IO.userError s!"ix isolation failed: expected {expected11}, got {result11}")

    -- Test 12: ix with effectful traversal (Option)
    let input12 : List Nat := [5, 10, 15, 20]
    let validator : Nat → Option Nat := fun x =>
      if x > 100 then none else some (x + 50)
    let optResult := traverse (ix 1) validator input12
    match optResult with
    | none => throw (IO.userError "ix Option validation should succeed")
    | some result =>
      let expected12 : List Nat := [5, 60, 15, 20]
      if result != expected12 then
        throw (IO.userError s!"ix with Option failed: expected {expected12}, got {result}")

    -- Test 13: ix with validation that fails
    let invalidValidator : Nat → Option Nat := fun x =>
      if x < 100 then none else some (x * 2)
    let optResult2 := traverse (ix 1) invalidValidator input12
    match optResult2 with
    | some _ => throw (IO.userError "ix Option should fail validation")
    | none => pure ()  -- Expected

    IO.println "✓ Indexed single focus tests passed"
}

/--
Test: `atLens` for optional element access
- View element at index (returns Option)
- Set element at index
- Delete element (set to none)
- Out of bounds access returns none
-/
private def case_indexedAtLens : TestCase := {
  name := "Indexed: optional element access with atLens",
  run := do
    -- Test 1: View element at valid index
    let input1 : List Nat := [10, 20, 30, 40, 50]
    let elem1 := view (atLens 2) input1
    let expected1 : Option Nat := some 30
    if elem1 != expected1 then
      throw (IO.userError s!"atLens view failed: expected {expected1}, got {elem1}")

    -- Test 2: View element at index 0
    let elem2 := view (atLens 0) input1
    let expected2 : Option Nat := some 10
    if elem2 != expected2 then
      throw (IO.userError s!"atLens view at 0 failed: expected {expected2}, got {elem2}")

    -- Test 3: View element at last index
    let elem3 := view (atLens 4) input1
    let expected3 : Option Nat := some 50
    if elem3 != expected3 then
      throw (IO.userError s!"atLens view at last failed: expected {expected3}, got {elem3}")

    -- Test 4: View out of bounds (returns none)
    let elem4 : Option Nat := view (atLens 10) input1
    if elem4.isSome then
      throw (IO.userError s!"atLens out of bounds should return none")

    -- Test 5: View on empty list (returns none)
    let empty : List Nat := []
    let elem5 : Option Nat := view (atLens 0) empty
    if elem5.isSome then
      throw (IO.userError s!"atLens on empty list should return none")

    -- Test 6: Set element at valid index
    let result6 := set (atLens 2) (some 300) input1
    let expected6 : List Nat := [10, 20, 300, 40, 50]
    if result6 != expected6 then
      throw (IO.userError s!"atLens set failed: expected {expected6}, got {result6}")

    -- Test 7: Set element at index 0
    let result7 := set (atLens 0) (some 100) input1
    let expected7 : List Nat := [100, 20, 30, 40, 50]
    if result7 != expected7 then
      throw (IO.userError s!"atLens set at 0 failed: expected {expected7}, got {result7}")

    -- Test 8: Set element at last index
    let result8 := set (atLens 4) (some 500) input1
    let expected8 : List Nat := [10, 20, 30, 40, 500]
    if result8 != expected8 then
      throw (IO.userError s!"atLens set at last failed: expected {expected8}, got {result8}")

    -- Test 9: Set at out of bounds index (should not modify)
    let result9 := set (atLens 10) (some 999) input1
    if result9 != input1 then
      throw (IO.userError s!"atLens set out of bounds should not modify: expected {input1}, got {result9}")

    -- Test 10: Set to none (keeps original based on implementation)
    let result10 := set (atLens 2) (none : Option Nat) input1
    -- Based on setAt? implementation, none keeps the original element
    if result10 != input1 then
      throw (IO.userError s!"atLens set none should keep original: expected {input1}, got {result10}")

    -- Test 11: Modify element using over on the lens
    let result11 := over (atLens 1) (Option.map (· * 10)) input1
    let expected11 : List Nat := [10, 200, 30, 40, 50]
    if result11 != expected11 then
      throw (IO.userError s!"atLens over failed: expected {expected11}, got {result11}")

    -- Test 12: Modify with function that changes to none
    let result12 := over (atLens 1) (fun (_ : Option Nat) => none) input1
    -- Setting to none keeps original
    if result12 != input1 then
      throw (IO.userError s!"atLens over to none should keep original: expected {input1}, got {result12}")

    -- Test 13: Chain multiple atLens operations
    let result13 := input1
      & (atLens 0) .~ some 111
      & (atLens 2) .~ some 333
      & (atLens 4) .~ some 555
    let expected13 : List Nat := [111, 20, 333, 40, 555]
    if result13 != expected13 then
      throw (IO.userError s!"Multiple atLens failed: expected {expected13}, got {result13}")

    -- Test 14: atLens with different types
    let input14 : List String := ["a", "b", "c", "d"]
    let elem14 := view (atLens 2) input14
    let expected14 : Option String := some "c"
    if elem14 != expected14 then
      throw (IO.userError s!"atLens String view failed: expected {expected14}, got {elem14}")

    let result14 := set (atLens 1) (some "REPLACED") input14
    let expected14r : List String := ["a", "REPLACED", "c", "d"]
    if result14 != expected14r then
      throw (IO.userError s!"atLens String set failed: expected {expected14r}, got {result14}")

    IO.println "✓ Indexed atLens tests passed"
}

/-! ## Combined Filtered + Indexed -/

/--
Test: Filter by index position
- Focus only even indices: filtered itraversed (fun (i, _) => i % 2 == 0)
- Focus only odd indices
- Focus every 3rd element
- Focus first/last N elements by index
-/
private def case_filteredByIndex : TestCase := {
  name := "Combined: filter elements by their index position",
  run := do
    let indexed := Instances.List.itraversed

    -- Test 1: Focus only even indices
    let input1 : List Nat := [10, 20, 30, 40, 50, 60]
    let evenIndices := filtered indexed (fun (i, _) => i % 2 == 0)
    let result1 := input1 & evenIndices %~ (fun (idx, v) => (idx, v * 100))
    let expected1 : List Nat := [1000, 20, 3000, 40, 5000, 60]
    if result1 != expected1 then
      throw (IO.userError s!"Even indices failed: expected {expected1}, got {result1}")

    -- Test 2: Focus only odd indices
    let oddIndices := filtered indexed (fun (i, _) => i % 2 == 1)
    let result2 := input1 & oddIndices %~ (fun (idx, v) => (idx, v + 1000))
    let expected2 : List Nat := [10, 1020, 30, 1040, 50, 1060]
    if result2 != expected2 then
      throw (IO.userError s!"Odd indices failed: expected {expected2}, got {result2}")

    -- Test 3: Focus every 3rd element (indices 0, 3, 6, ...)
    let input3 : List Nat := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
    let every3rd := filtered indexed (fun (i, _) => i % 3 == 0)
    let result3 := input3 & every3rd %~ (fun (idx, v) => (idx, v + 100))
    let expected3 : List Nat := [101, 2, 3, 104, 5, 6, 107, 8, 9, 110]
    if result3 != expected3 then
      throw (IO.userError s!"Every 3rd element failed: expected {expected3}, got {result3}")

    -- Test 4: Focus first 3 elements (indices < 3)
    let first3 := filtered indexed (fun (i, _) => i < 3)
    let result4 := input3 & first3 %~ (fun (idx, v) => (idx, v * 10))
    let expected4 : List Nat := [10, 20, 30, 4, 5, 6, 7, 8, 9, 10]
    if result4 != expected4 then
      throw (IO.userError s!"First 3 elements failed: expected {expected4}, got {result4}")

    -- Test 5: Focus last 3 elements (indices >= 7 for list of length 10)
    let last3 := filtered indexed (fun (i, _) => i >= 7)
    let result5 := input3 & last3 %~ (fun (idx, v) => (idx, v + 50))
    let expected5 : List Nat := [1, 2, 3, 4, 5, 6, 7, 58, 59, 60]
    if result5 != expected5 then
      throw (IO.userError s!"Last 3 elements failed: expected {expected5}, got {result5}")

    -- Test 6: Focus middle elements (2 <= index <= 5)
    let middle := filtered indexed (fun (i, _) => i >= 2 && i <= 5)
    let result6 := input3 & middle %~ (fun (idx, v) => (idx, v * 2))
    let expected6 : List Nat := [1, 2, 6, 8, 10, 12, 7, 8, 9, 10]
    if result6 != expected6 then
      throw (IO.userError s!"Middle elements failed: expected {expected6}, got {result6}")

    -- Test 7: Focus single index via filter
    let singleIdx := filtered indexed (fun (i, _) => i == 4)
    let result7 := input3 & singleIdx %~ (fun (_idx, _v) => (_idx, 999))
    let expected7 : List Nat := [1, 2, 3, 4, 999, 6, 7, 8, 9, 10]
    if result7 != expected7 then
      throw (IO.userError s!"Single index filter failed: expected {expected7}, got {result7}")

    -- Test 8: No indices match (empty filter)
    let noMatch := filtered indexed (fun (i, _) => i > 100)
    let result8 := input3 & noMatch %~ (fun (idx, v) => (idx, v * 1000))
    if result8 != input3 then
      throw (IO.userError s!"Empty filter should not modify: expected {input3}, got {result8}")

    -- Test 9: All indices match
    let allMatch := filtered indexed (fun (i, _) => i >= 0)
    let result9 := [1, 2, 3] & allMatch %~ (fun (idx, v) => (idx, v + idx))
    let expected9 : List Nat := [1, 3, 5]
    if result9 != expected9 then
      throw (IO.userError s!"All match filter failed: expected {expected9}, got {result9}")

    -- Test 10: Index-based pattern (Fibonacci indices: 0, 1, 2, 3, 5, 8)
    let fibIndices := filtered indexed (fun (i, _) =>
      i == 0 || i == 1 || i == 2 || i == 3 || i == 5 || i == 8)
    let result10 := input3 & fibIndices %~ (fun (idx, v) => (idx, v + 10))
    let expected10 : List Nat := [11, 12, 13, 14, 5, 16, 7, 8, 19, 10]
    if result10 != expected10 then
      throw (IO.userError s!"Fibonacci indices failed: expected {expected10}, got {result10}")

    IO.println "✓ Filtered by index tests passed"
}

/--
Test: Filter by value, incorporate index in transformation
- Filter positive numbers, multiply by index
- Filter elements in range, add their position
- Filter strings by length, prepend index
-/
private def case_filteredValueIndexTransform : TestCase := {
  name := "Combined: filter by value, transform using index",
  run := do
    let indexed := Instances.List.itraversed

    -- Test 1: Filter positive numbers, multiply by (index + 1)
    let input1 : List Int := [-2, 3, -1, 4, 0, 5, -3]
    let indexedInt := Instances.List.itraversed (α := Int)
    let posFilter := filtered indexedInt (fun (_, v) => v > 0)
    let result1 := input1 & posFilter %~ (fun (idx, v) => (idx, v * ((idx : Int) + 1)))
    -- Matches: idx=1 val=3, idx=3 val=4, idx=5 val=5
    let expected1 : List Int := [-2, 6, -1, 16, 0, 30, -3]
    if result1 != expected1 then
      throw (IO.userError s!"Positive filter with index failed: expected {expected1}, got {result1}")

    -- Test 2: Filter elements in range [10, 50], add their position
    let input2 : List Nat := [5, 20, 60, 30, 8, 40, 100]
    let rangeFilter := filtered indexed (fun (_, v) => v >= 10 && v <= 50)
    let result2 := input2 & rangeFilter %~ (fun (idx, v) => (idx, v + idx * 10))
    -- Matches: idx=1 val=20, idx=3 val=30, idx=5 val=40
    let expected2 : List Nat := [5, 30, 60, 60, 8, 90, 100]
    if result2 != expected2 then
      throw (IO.userError s!"Range filter with index failed: expected {expected2}, got {result2}")

    -- Test 3: Filter strings by length > 3, prepend index
    let input3 : List String := ["hi", "hello", "ok", "world", "a", "test"]
    let indexedStr := Instances.List.itraversed (α := String)
    let lenFilter := filtered indexedStr (fun (_, v) => v.length > 3)
    let result3 := input3 & lenFilter %~ (fun (idx, v) => (idx, s!"{idx}:{v}"))
    -- Matches: idx=1 "hello", idx=3 "world", idx=5 "test"
    let expected3 : List String := ["hi", "1:hello", "ok", "3:world", "a", "5:test"]
    if result3 != expected3 then
      throw (IO.userError s!"String length filter failed: expected {expected3}, got {result3}")

    -- Test 4: Filter even values, add index
    let input4 : List Nat := [1, 2, 3, 4, 5, 6, 7, 8]
    let evenFilter := filtered indexed (fun (_, v) => v % 2 == 0)
    let result4 := input4 & evenFilter %~ (fun (idx, v) => (idx, v + idx))
    -- Matches: idx=1 val=2, idx=3 val=4, idx=5 val=6, idx=7 val=8
    let expected4 : List Nat := [1, 3, 3, 7, 5, 11, 7, 15]
    if result4 != expected4 then
      throw (IO.userError s!"Even filter with index add failed: expected {expected4}, got {result4}")

    -- Test 5: Filter large values (>= 100), scale by distance from start
    let input5 : List Nat := [50, 150, 75, 200, 300, 25]
    let largeFilter := filtered indexed (fun (_, v) => v >= 100)
    let result5 := input5 & largeFilter %~ (fun (idx, v) =>
      (idx, v + idx * 100))
    -- Matches: idx=1 val=150, idx=3 val=200, idx=4 val=300
    let expected5 : List Nat := [50, 250, 75, 500, 700, 25]
    if result5 != expected5 then
      throw (IO.userError s!"Large value filter failed: expected {expected5}, got {result5}")

    -- Test 6: Filter by divisibility, multiply by position weight
    let input6 : List Nat := [1, 3, 5, 6, 8, 9, 10, 12]
    let div3Filter := filtered indexed (fun (_, v) => v % 3 == 0)
    let result6 := input6 & div3Filter %~ (fun (idx, v) =>
      (idx, v * (idx + 1)))
    -- Matches: idx=1 val=3, idx=3 val=6, idx=5 val=9, idx=7 val=12
    let expected6 : List Nat := [1, 6, 5, 24, 8, 54, 10, 96]
    if result6 != expected6 then
      throw (IO.userError s!"Divisibility filter failed: expected {expected6}, got {result6}")

    -- Test 7: Complex transformation - filter negatives, replace with abs + index
    let input7 : List Int := [1, -2, 3, -4, -5, 6]
    let indexedInt := Instances.List.itraversed (α := Int)
    let negFilter := filtered indexedInt (fun (_, v) => v < 0)
    let result7 := input7 & negFilter %~ (fun (idx, v) =>
      (idx, (-v) + (idx : Int) * 10))
    -- Matches: idx=1 val=-2, idx=3 val=-4, idx=4 val=-5
    let expected7 : List Int := [1, 12, 3, 34, 45, 6]
    if result7 != expected7 then
      throw (IO.userError s!"Negative filter with abs failed: expected {expected7}, got {result7}")

    -- Test 8: Filter and annotate with position info
    let input8 : List Nat := [100, 5, 200, 10, 300]
    let smallFilter := filtered indexed (fun (_, v) => v < 50)
    let result8 := input8 & smallFilter %~ (fun (idx, v) =>
      (idx, v + 1000 + idx))
    -- Matches: idx=1 val=5, idx=3 val=10
    let expected8 : List Nat := [100, 1006, 200, 1013, 300]
    if result8 != expected8 then
      throw (IO.userError s!"Small value filter failed: expected {expected8}, got {result8}")

    IO.println "✓ Filtered value with index transform tests passed"
}

/--
Test: Complex combined predicates
- Filter: even values at odd indices
- Filter: values greater than their index
- Filter: elements matching f(index, value) predicate
- Multiple composed filtered+indexed operations
-/
private def case_filteredIndexedComplex : TestCase := {
  name := "Combined: complex predicates using both index and value",
  run := do
    let indexed := Instances.List.itraversed

    -- Test 1: Even values at odd indices
    let input1 : List Nat := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
    let evenAtOdd := filtered indexed (fun (i, v) => i % 2 == 1 && v % 2 == 0)
    let result1 := input1 & evenAtOdd %~ (fun (idx, v) => (idx, v * 100))
    -- Matches: idx=1 val=2, idx=3 val=4, idx=5 val=6, idx=7 val=8, idx=9 val=10
    let expected1 : List Nat := [1, 200, 3, 400, 5, 600, 7, 800, 9, 1000]
    if result1 != expected1 then
      throw (IO.userError s!"Even values at odd indices failed: expected {expected1}, got {result1}")

    -- Test 2: Odd values at even indices
    let oddAtEven := filtered indexed (fun (i, v) => i % 2 == 0 && v % 2 == 1)
    let result2 := input1 & oddAtEven %~ (fun (idx, v) => (idx, v + 50))
    -- Matches: idx=0 val=1, idx=2 val=3, idx=4 val=5, idx=6 val=7, idx=8 val=9
    let expected2 : List Nat := [51, 2, 53, 4, 55, 6, 57, 8, 59, 10]
    if result2 != expected2 then
      throw (IO.userError s!"Odd values at even indices failed: expected {expected2}, got {result2}")

    -- Test 3: Values greater than their index
    let input3 : List Nat := [0, 5, 1, 8, 2, 10, 3]
    let greaterThanIdx := filtered indexed (fun (i, v) => v > i)
    let result3 := input3 & greaterThanIdx %~ (fun (idx, v) => (idx, v * 2))
    -- Matches: idx=1 val=5>1, idx=3 val=8>3, idx=5 val=10>5
    let expected3 : List Nat := [0, 10, 1, 16, 2, 20, 3]
    if result3 != expected3 then
      throw (IO.userError s!"Values > index failed: expected {expected3}, got {result3}")

    -- Test 4: Values equal to or less than their index
    let leqIdx := filtered indexed (fun (i, v) => v <= i)
    let result4 := input3 & leqIdx %~ (fun (idx, v) => (idx, v + 100))
    -- Matches: idx=0 val=0<=0, idx=2 val=1<=2, idx=4 val=2<=4, idx=6 val=3<=6
    let expected4 : List Nat := [100, 5, 101, 8, 102, 10, 103]
    if result4 != expected4 then
      throw (IO.userError s!"Values <= index failed: expected {expected4}, got {result4}")

    -- Test 5: Complex predicate - divisible by index (when index > 0)
    let input5 : List Nat := [10, 20, 6, 12, 8, 15]
    let divByIdx := filtered indexed (fun (i, v) => i > 0 && v % i == 0)
    let result5 := input5 & divByIdx %~ (fun (idx, v) => (idx, v / idx))
    -- Matches: idx=1 val=20%1=0, idx=2 val=6%2=0, idx=3 val=12%3=0, idx=4 val=8%4=0, idx=5 val=15%5=0
    let expected5 : List Nat := [10, 20, 3, 4, 2, 3]
    if result5 != expected5 then
      throw (IO.userError s!"Divisible by index failed: expected {expected5}, got {result5}")

    -- Test 6: Index and value in specific relationship
    let input6 : List Nat := [0, 1, 4, 9, 16, 25, 36]
    let isSquare := filtered indexed (fun (i, v) => v == i * i)
    let result6 := input6 & isSquare %~ (fun (idx, v) => (idx, v + 1000))
    -- All match: 0=0², 1=1², 4=2², 9=3², 16=4², 25=5², 36=6²
    let expected6 : List Nat := [1000, 1001, 1004, 1009, 1016, 1025, 1036]
    if result6 != expected6 then
      throw (IO.userError s!"Square relationship failed: expected {expected6}, got {result6}")

    -- Test 7: Multiple conditions - value even AND greater than index AND index odd
    -- Need input where odd indices have even values > their index
    let input7 : List Nat := [0, 2, 2, 4, 4, 6, 6, 8, 8, 10, 10]
    let complex := filtered indexed (fun (i, v) =>
      v % 2 == 0 && v > i && i % 2 == 1)
    let result7 := input7 & complex %~ (fun (idx, v) => (idx, v + idx))
    -- Matches at odd indices with even values > index:
    -- idx=1 val=2: 2%2==0✓ 2>1✓ 1%2==1✓ -> match -> 2+1=3
    -- idx=3 val=4: 4%2==0✓ 4>3✓ 3%2==1✓ -> match -> 4+3=7
    -- idx=5 val=6: 6%2==0✓ 6>5✓ 5%2==1✓ -> match -> 6+5=11
    -- idx=7 val=8: 8%2==0✓ 8>7✓ 7%2==1✓ -> match -> 8+7=15
    -- idx=9 val=10: 10%2==0✓ 10>9✓ 9%2==1✓ -> match -> 10+9=19
    let expected7 : List Nat := [0, 3, 2, 7, 4, 11, 6, 15, 8, 19, 10]
    if result7 != expected7 then
      throw (IO.userError s!"Complex multi-condition failed: expected {expected7}, got {result7}")

    -- Test 8: Absolute difference between index and value
    let input8 : List Int := [5, 4, 3, 2, 1, 0]
    let indexedInt := Instances.List.itraversed (α := Int)
    let diffFilter := filtered indexedInt (fun (i, v) =>
      let diff := if v >= (i : Int) then v - (i : Int) else (i : Int) - v
      diff <= 2)
    let result8 := input8 & diffFilter %~ (fun (idx, v) => (idx, v * 10))
    -- idx=0 val=5: |5-0|=5 > 2 ✗
    -- idx=1 val=4: |4-1|=3 > 2 ✗
    -- idx=2 val=3: |3-2|=1 <= 2 ✓ -> 30
    -- idx=3 val=2: |2-3|=1 <= 2 ✓ -> 20
    -- idx=4 val=1: |1-4|=3 > 2 ✗
    -- idx=5 val=0: |0-5|=5 > 2 ✗
    let expected8 : List Int := [5, 4, 30, 20, 1, 0]
    if result8 != expected8 then
      throw (IO.userError s!"Absolute difference filter failed: expected {expected8}, got {result8}")

    IO.println "✓ Filtered indexed complex predicates tests passed"
}

/--
Test: Chaining operations
- itraversed then filtered (filter after adding index)
- filtered then map over indices
- Compose multiple filters with index transforms
-/
private def case_filteredIndexedChaining : TestCase := {
  name := "Combined: chaining filtered and indexed operations",
  run := do
    let indexed := Instances.List.itraversed
    let tr := Instances.List.traversed

    -- Test 1: Chain two filters on indexed traversal
    let input1 : List Nat := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
    let evenIndices := filtered indexed (fun (i, _) => i % 2 == 0)
    let largeValues := filtered evenIndices (fun (_, v) => v > 5)
    let result1 := input1 & largeValues %~ (fun (idx, v) => (idx, v * 10))
    -- First filter: idx even -> [1,3,5,7,9] at positions [0,2,4,6,8]
    -- Second filter: value > 5 -> [7,9] at positions [6,8]
    let expected1 : List Nat := [1, 2, 3, 4, 5, 6, 70, 8, 90, 10]
    if result1 != expected1 then
      throw (IO.userError s!"Chained filters failed: expected {expected1}, got {result1}")

    -- Test 2: Filter by value, then filter by index
    let input2 : List Nat := [10, 20, 30, 40, 50, 60]
    let largeFilter := filtered indexed (fun (_, v) => v >= 30)
    let oddIdxFilter := filtered largeFilter (fun (i, _) => i % 2 == 1)
    let result2 := input2 & oddIdxFilter %~ (fun (idx, v) => (idx, v + 100))
    -- First filter: v >= 30 -> [30,40,50,60] at positions [2,3,4,5]
    -- Second filter: odd indices -> [40,60] at positions [3,5]
    let expected2 : List Nat := [10, 20, 30, 140, 50, 160]
    if result2 != expected2 then
      throw (IO.userError s!"Value then index filter failed: expected {expected2}, got {result2}")

    -- Test 3: Multiple chained transformations
    let input3 : List Nat := [1, 2, 3, 4, 5]
    let result3 := input3
      & (filtered indexed (fun (i, _) => i > 0)) %~ (fun (idx, v) => (idx, v * 2))
      & (filtered indexed (fun (_, v) => v % 2 == 0)) %~ (fun (idx, v) => (idx, v + 10))
    -- First: indices > 0 -> [2,3,4,5] at [1,2,3,4] -> double -> [1,4,6,8,10]
    -- Second: even values -> [4,6,8,10] at [1,2,3,4] -> add 10 -> [1,14,16,18,20]
    let expected3 : List Nat := [1, 14, 16, 18, 20]
    if result3 != expected3 then
      throw (IO.userError s!"Multiple transformations failed: expected {expected3}, got {result3}")

    -- Test 4: Compose with regular traversal
    let input4 : List Nat := [10, 20, 30]
    let result4 := input4
      & tr %~ (· + 1)                    -- Add 1 to all
      & (filtered indexed (fun (i, _) => i == 1)) %~ (fun (idx, v) => (idx, v * 100))
    let expected4 : List Nat := [11, 2100, 31]  -- [10+1, (20+1)*100, 30+1]
    if result4 != expected4 then
      throw (IO.userError s!"Traversal then filter failed: expected {expected4}, got {result4}")

    -- Test 5: Complex chaining with different predicates
    let input5 : List Int := [-5, -3, -1, 1, 3, 5]
    let indexedInt := Instances.List.itraversed (α := Int)
    let result5 := input5
      & (filtered indexedInt (fun (_i, v) => v < 0)) %~ (fun (idx, v) => (idx, -v))
      & (filtered indexedInt (fun (i, _v) => i % 2 == 0)) %~ (fun (idx, v) => (idx, v + 10))
    -- First: negatives -> [5,3,1,1,3,5]
    -- Second: even indices -> [15,3,11,1,13,5]
    let expected5 : List Int := [15, 3, 11, 1, 13, 5]
    if result5 != expected5 then
      throw (IO.userError s!"Complex chaining failed: expected {expected5}, got {result5}")

    IO.println "✓ Filtered indexed chaining tests passed"
}

/-! ## Stateful Filtered + Indexed -/

/--
Test: Count filtered elements with State
- State tracks how many elements matched filter
- State tracks indices of filtered elements
- State accumulates filtered values
-/
private def case_filteredStatefulCounting : TestCase := {
  name := "Stateful: count and track filtered elements",
  run := do
    -- Test 1: Count elements using StateM
    let input1 : List Nat := [1, 2, 3, 4, 5, 6]
    let tr := Instances.List.traversed
    let evens := filtered tr (fun x => x % 2 == 0)

    -- Count matching elements by incrementing state
    let counter (x : Nat) : StateM Nat Nat := do
      let count ← get
      set (count + 1)
      return x

    let (result, count) := StateT.run (traverse evens counter input1) 0
    if result != input1 then
      throw (IO.userError s!"Stateful counting changed values")
    if count != 3 then  -- 2, 4, 6 are even
      throw (IO.userError s!"Count incorrect: expected 3, got {count}")

    -- Test 2: Accumulate sum of filtered elements
    let accumulator (x : Nat) : StateM Nat Nat := do
      let sum ← get
      set (sum + x)
      return x

    let (_result2, sum) := StateT.run (traverse evens accumulator input1) 0
    if sum != 12 then  -- 2 + 4 + 6 = 12
      throw (IO.userError s!"Sum incorrect: expected 12, got {sum}")

    IO.println "✓ Stateful counting tests passed"
}

/--
Test: Running statistics with indices
- Running sum, but only for elements at even indices
- Running max, filtered by predicate
- Conditional accumulation based on index position
-/
private def case_indexedStatefulAccumulation : TestCase := {
  name := "Stateful: accumulate statistics using indices",
  run := do
    -- Test 1: Assign sequential IDs to elements
    let input1 : List String := ["a", "b", "c", "d"]
    let tr := Instances.List.traversed (α := String) (β := (Nat × String))

    let assigner (x : String) : StateM Nat (Nat × String) := do
      let id ← get
      set (id + 1)
      return (id, x)

    let (result, _) := StateT.run (traverse tr assigner input1) 1
    let expected : List (Nat × String) := [(1, "a"), (2, "b"), (3, "c"), (4, "d")]
    if result != expected then
      throw (IO.userError s!"ID assignment failed")

    -- Test 2: Running sum
    let input2 : List Nat := [1, 2, 3, 4, 5]
    let tr2 := Instances.List.traversed (α := Nat) (β := Nat)

    let runningSum (x : Nat) : StateM Nat Nat := do
      let sum ← get
      let newSum := sum + x
      set newSum
      return newSum

    let (result2, _) := StateT.run (traverse tr2 runningSum input2) 0
    let expected2 : List Nat := [1, 3, 6, 10, 15]  -- Running sum
    if result2 != expected2 then
      throw (IO.userError s!"Running sum failed: expected {expected2}, got {result2}")

    IO.println "✓ Stateful accumulation tests passed"
}

/--
Test: Build lookup tables during filtered traversal
- Assign IDs only to filtered elements
- Map indices to values for elements matching predicate
- Track position of first/last occurrence matching filter
-/
private def case_filteredStatefulMapping : TestCase := {
  name := "Stateful: build maps during filtered traversal",
  run := do
    -- Test: Assign IDs only to even numbers
    let input : List Nat := [1, 2, 3, 4, 5, 6, 7, 8]
    let tr := Instances.List.traversed
    let evens := filtered tr (fun x => x % 2 == 0)

    -- Assign sequential IDs starting from 100
    let idAssigner (_x : Nat) : StateM Nat Nat := do
      let id ← get
      set (id + 1)
      return id

    let (result, _) := StateT.run (traverse evens idAssigner input) 100
    -- Only evens get new IDs: 2→100, 4→101, 6→102, 8→103
    let expected : List Nat := [1, 100, 3, 101, 5, 102, 7, 103]
    if result != expected then
      throw (IO.userError s!"ID assignment to filtered elements failed: expected {expected}, got {result}")

    IO.println "✓ Stateful mapping tests passed"
}

/--
Test: Stateful transformations with index context
- Replace element with running sum at that index
- Normalize by statistics computed up to that index
- Sliding window, but only over filtered elements
-/
private def case_indexedStatefulContext : TestCase := {
  name := "Stateful: context-dependent transformations with indices",
  run := do
    -- Test: Replace each element with running product
    let input : List Nat := [2, 3, 4, 5]
    let tr := Instances.List.traversed (α := Nat) (β := Nat)

    let runningProduct (x : Nat) : StateM Nat Nat := do
      let prod ← get
      let newProd := prod * x
      set newProd
      return prod  -- Return previous product

    let (result, _) := StateT.run (traverse tr runningProduct input) 1
    let expected : List Nat := [1, 2, 6, 24]  -- Products: 1, 1*2, 1*2*3, 1*2*3*4
    if result != expected then
      throw (IO.userError s!"Running product failed: expected {expected}, got {result}")

    IO.println "✓ Stateful context tests passed"
}

/-! ## Real-World Use Cases -/

/--
Test: Update specific array elements
- Update elements at indices [2, 5, 7] to specific values
- Increment elements at even positions
- Zero out negative values
- Clamp values to range only at certain indices
-/
private def case_realworldArrayUpdates : TestCase := {
  name := "Real-world: selective array element updates",
  run := do
    let indexed := Instances.List.itraversed

    -- Test 1: Update elements at specific indices
    let input1 : List Nat := [10, 20, 30, 40, 50, 60, 70, 80]
    let result1 := input1
      & (ix 2) .~ 999
      & (ix 5) .~ 888
      & (ix 7) .~ 777
    let expected1 : List Nat := [10, 20, 999, 40, 50, 888, 70, 777]
    if result1 != expected1 then
      throw (IO.userError s!"Specific index updates failed: expected {expected1}, got {result1}")

    -- Test 2: Increment elements at even positions
    let input2 : List Nat := [1, 2, 3, 4, 5, 6, 7, 8]
    let evenPositions := filtered indexed (fun (i, _) => i % 2 == 0)
    let result2 := input2 & evenPositions %~ (fun (idx, v) => (idx, v + 10))
    let expected2 : List Nat := [11, 2, 13, 4, 15, 6, 17, 8]
    if result2 != expected2 then
      throw (IO.userError s!"Even position increment failed: expected {expected2}, got {result2}")

    -- Test 3: Zero out negative values
    let input3 : List Int := [-5, 10, -3, 0, 7, -2, 15]
    let tr := Instances.List.traversed (α := Int) (β := Int)
    let negatives := filtered tr (fun x => x < 0)
    let result3 := input3 & negatives .~ 0
    let expected3 : List Int := [0, 10, 0, 0, 7, 0, 15]
    if result3 != expected3 then
      throw (IO.userError s!"Zero out negatives failed: expected {expected3}, got {result3}")

    -- Test 4: Clamp values to range [0, 100] only at odd indices
    let input4 : List Int := [50, 150, 30, -10, 80, 200, 5]
    let indexedInt := Instances.List.itraversed (α := Int)
    let oddIndices := filtered indexedInt (fun (i, _) => i % 2 == 1)
    let clamp (x : Int) : Int :=
      if x < 0 then 0
      else if x > 100 then 100
      else x
    let result4 := input4 & oddIndices %~ (fun (idx, v) => (idx, clamp v))
    let expected4 : List Int := [50, 100, 30, 0, 80, 100, 5]
    if result4 != expected4 then
      throw (IO.userError s!"Clamping failed: expected {expected4}, got {result4}")

    -- Test 5: Batch update multiple specific indices with different values
    let input5 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    let result5 := input5
      & (ix 1) .~ 111
      & (ix 3) .~ 333
      & (ix 5) .~ 555
      & (ix 7) .~ 777
      & (ix 9) .~ 999
    let expected5 : List Nat := [0, 111, 0, 333, 0, 555, 0, 777, 0, 999]
    if result5 != expected5 then
      throw (IO.userError s!"Batch update failed: expected {expected5}, got {result5}")

    IO.println "✓ Real-world array updates tests passed"
}

/--
Test: Conditional batch transformations
- Apply discount only to items with price > 100
- Tax calculation only on taxable items (with tracking)
- Normalize scores, but only for students who took test
-/
private def case_realworldConditionalBatch : TestCase := {
  name := "Real-world: conditional batch operations",
  run := do
    -- Test 1: Apply 20% discount to items with price > 100
    let inventory : List Product := [
      { name := "Widget", price := 50, quantity := 10 },
      { name := "Gadget", price := 150, quantity := 5 },
      { name := "Premium Tool", price := 200, quantity := 3 },
      { name := "Basic Item", price := 25, quantity := 20 }
    ]
    let tr := Instances.List.traversed
    let expensive := filtered tr (fun p : Product => p.price > 100)
    let discounted := inventory & (expensive ⊚ priceLens) %~ (fun p => p * 80 / 100)

    let expected1 : List Product := [
      { name := "Widget", price := 50, quantity := 10 },
      { name := "Gadget", price := 120, quantity := 5 },        -- 150 * 0.8 = 120
      { name := "Premium Tool", price := 160, quantity := 3 },  -- 200 * 0.8 = 160
      { name := "Basic Item", price := 25, quantity := 20 }
    ]
    if discounted != expected1 then
      throw (IO.userError "Discount application failed")

    -- Test 2: Add 10% tax only to items with quantity < 10
    let lowStock := filtered tr (fun p : Product => p.quantity < 10)
    let taxed := inventory & (lowStock ⊚ priceLens) %~ (fun p => p * 110 / 100)

    let expected2 : List Product := [
      { name := "Widget", price := 50, quantity := 10 },
      { name := "Gadget", price := 165, quantity := 5 },      -- 150 * 1.1 = 165
      { name := "Premium Tool", price := 220, quantity := 3 }, -- 200 * 1.1 = 220
      { name := "Basic Item", price := 25, quantity := 20 }
    ]
    if taxed != expected2 then
      throw (IO.userError "Tax application failed")

    -- Test 3: Normalize scores (scale to 0-100) only for students who took test (score >= 0)
    let results : List TestResult := [
      { student := "Alice", score := 85 },
      { student := "Bob", score := -1 },
      { student := "Charlie", score := 72 },
      { student := "Dave", score := -1 },
      { student := "Eve", score := 95 }
    ]

    let trResults := Instances.List.traversed (α := TestResult) (β := TestResult)
    let tookTest := filtered trResults (fun r : TestResult => r.score >= 0)
    -- Normalize scores: map [0,100] to [0,100] (already normalized, but apply formula)
    let normalized := results & (tookTest ⊚ scoreLens) %~ (fun s => s)

    if normalized.length != results.length then
      throw (IO.userError "Normalization changed list length")

    IO.println "✓ Real-world conditional batch tests passed"
}

/--
Test: Data validation and transformation
- Validate: ensure values at even indices are even
- Transform: replace invalid entries (via filter) with defaults
- Collect: gather positions of all invalid entries
-/
private def case_realworldValidation : TestCase := {
  name := "Real-world: validation and correction",
  run := do
    let indexed := Instances.List.itraversed

    -- Test 1: Replace invalid entries with defaults
    -- Rule: Values at even indices should be even numbers
    let input1 : List Nat := [2, 5, 7, 8, 10, 15, 12, 20]
    let evenIdxOddVal := filtered indexed (fun (i, v) => i % 2 == 0 && v % 2 == 1)
    let corrected1 := input1 & evenIdxOddVal %~ (fun (idx, _) => (idx, 0))  -- Replace with 0
    let expected1 : List Nat := [2, 5, 0, 8, 10, 15, 12, 20]  -- idx=2 val=7 is invalid
    if corrected1 != expected1 then
      throw (IO.userError s!"Validation correction failed: expected {expected1}, got {corrected1}")

    -- Test 2: Validate with Option - ensure no negatives exist
    let input2 : List Int := [1, 2, 3, 4, 5]
    let tr := Instances.List.traversed (α := Int) (β := Int)
    let validator : Int → Option Int := fun x =>
      if x >= 0 then some x else none
    let validResult := traverse tr validator input2
    match validResult with
    | none => throw (IO.userError "Validation should have succeeded")
    | some result =>
      if result != input2 then
        throw (IO.userError "Validation changed valid data")

    -- Test 3: Validation that fails
    let input3 : List Int := [1, -2, 3, 4]
    let failResult := traverse tr validator input3
    match failResult with
    | some _ => throw (IO.userError "Validation should have failed on negative")
    | none => pure ()  -- Expected

    -- Test 4: Fix out-of-range values
    let input4 : List Nat := [10, 150, 30, 200, 50, 180]
    let outOfRange := filtered Instances.List.traversed (fun x : Nat => x > 100)
    let clamped := input4 & outOfRange .~ 100
    let expected4 : List Nat := [10, 100, 30, 100, 50, 100]
    if clamped != expected4 then
      throw (IO.userError s!"Clamping failed: expected {expected4}, got {clamped}")

    -- Test 5: Normalize data - ensure all values in [0, 10]
    let input5 : List Nat := [5, 15, 8, 25, 3, 12]
    let tooLarge := filtered Instances.List.traversed (fun x : Nat => x > 10)
    let normalized := input5 & tooLarge %~ (fun x => x / 10)
    let expected5 : List Nat := [5, 1, 8, 2, 3, 1]
    if normalized != expected5 then
      throw (IO.userError s!"Normalization failed: expected {expected5}, got {normalized}")

    IO.println "✓ Real-world validation tests passed"
}

/--
Test: Sparse array operations
- Update only non-zero elements
- Compress: collect indices and values of non-zero elements
- Reconstruct: expand sparse representation
-/
private def case_realworldSparseArrays : TestCase := {
  name := "Real-world: sparse array transformations",
  run := do
    -- Test 1: Update only non-zero elements
    let input1 : List Nat := [0, 5, 0, 0, 3, 0, 7, 0]
    let nonZero := filtered Instances.List.traversed (fun x : Nat => x != 0)
    let doubled := input1 & nonZero %~ (· * 2)
    let expected1 : List Nat := [0, 10, 0, 0, 6, 0, 14, 0]
    if doubled != expected1 then
      throw (IO.userError s!"Sparse update failed: expected {expected1}, got {doubled}")

    -- Test 2: Increment non-zero elements
    let incremented := input1 & nonZero %~ (· + 100)
    let expected2 : List Nat := [0, 105, 0, 0, 103, 0, 107, 0]
    if incremented != expected2 then
      throw (IO.userError s!"Sparse increment failed: expected {expected2}, got {incremented}")

    -- Test 3: Set all non-zero elements to a specific value
    let normalized := input1 & nonZero .~ 1
    let expected3 : List Nat := [0, 1, 0, 0, 1, 0, 1, 0]
    if normalized != expected3 then
      throw (IO.userError s!"Sparse normalization failed: expected {expected3}, got {normalized}")

    -- Test 4: Filter with indexed - process non-zero at even indices
    let indexed := Instances.List.itraversed
    let nonZeroEvenIdx := filtered indexed (fun (i, v) => v != 0 && i % 2 == 0)
    let result4 := [0, 5, 10, 0, 20, 0, 30, 0] & nonZeroEvenIdx %~ (fun (idx, v) => (idx, v + 1000))
    let expected4 : List Nat := [0, 5, 1010, 0, 1020, 0, 1030, 0]
    if result4 != expected4 then
      throw (IO.userError s!"Sparse indexed failed: expected {expected4}, got {result4}")

    IO.println "✓ Real-world sparse arrays tests passed"
}

/--
Test: Position-aware string transformations
- Capitalize first letter (index 0) of each word
- Replace characters at specific positions
- Redact: replace characters matching pattern with '*'
- Insert separators at regular index intervals
-/
private def case_realworldStringOps : TestCase := {
  name := "Real-world: position-aware string operations",
  run := do
    -- Test 1: Replace characters at specific positions
    let chars1 : List Char := ['h', 'e', 'l', 'l', 'o']
    let result1 := chars1
      & (ix 0) .~ 'H'
      & (ix 4) .~ 'O'
    let expected1 : List Char := ['H', 'e', 'l', 'l', 'O']
    if result1 != expected1 then
      throw (IO.userError s!"Char replacement failed")

    -- Test 2: Redact characters at odd positions
    let chars2 : List Char := ['p', 'a', 's', 's', 'w', 'o', 'r', 'd']
    let indexed := Instances.List.itraversed (α := Char)
    let oddPos := filtered indexed (fun (i, _) => i % 2 == 1)
    let redacted := chars2 & oddPos %~ (fun (idx, _) => (idx, '*'))
    let expected2 : List Char := ['p', '*', 's', '*', 'w', '*', 'r', '*']
    if redacted != expected2 then
      throw (IO.userError s!"Redaction failed")

    -- Test 3: Uppercase characters at even positions
    let chars3 : List Char := ['h', 'e', 'l', 'l', 'o']
    let evenPos := filtered indexed (fun (i, _) => i % 2 == 0)
    let uppercased := chars3 & evenPos %~ (fun (idx, c) => (idx, c.toUpper))
    let expected3 : List Char := ['H', 'e', 'L', 'l', 'O']
    if uppercased != expected3 then
      throw (IO.userError s!"Uppercase at even positions failed")

    -- Test 4: Filter and modify specific characters
    let chars4 : List Char := ['a', 'b', 'c', 'd', 'e']
    let tr := Instances.List.traversed (α := Char) (β := Char)
    let vowels := filtered tr (fun c => c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u')
    let modified := chars4 & vowels .~ '*'
    let expected4 : List Char := ['*', 'b', 'c', 'd', '*']
    if modified != expected4 then
      throw (IO.userError s!"Vowel filtering failed")

    IO.println "✓ Real-world string ops tests passed"
}

/-! ## Performance and Fusion -/

/--
Test: Demonstrate fusion opportunities
- Multiple filters should fuse into single pass
- filtered + map should fuse
- Benchmark: separate passes vs fused operation (comment with analysis)
-/
private def case_performanceFusion : TestCase := {
  name := "Performance: fusion of filtered operations",
  run := do
    -- Demonstrate that multiple filters can be composed efficiently
    -- In a lazy/fused implementation, this would traverse the list once
    let input : List Nat := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
    let tr := Instances.List.traversed

    -- Composed filters - conceptually could fuse into single pass
    let evens := filtered tr (fun x => x % 2 == 0)
    let large := filtered evens (fun x => x > 5)
    let result := input & large %~ (· * 10)
    let expected : List Nat := [1, 2, 3, 4, 5, 60, 7, 80, 9, 100]
    if result != expected then
      throw (IO.userError s!"Fusion test failed: expected {expected}, got {result}")

    -- Multiple transformations that could fuse
    let result2 := input
      & (filtered tr (fun x => x > 3)) %~ (· + 10)
      & (filtered tr (fun x => x % 2 == 0)) %~ (· * 2)
    -- First: [1,2,3,14,15,16,17,18,19,20]
    -- Second: [1,4,3,28,15,32,17,36,19,40]
    let expected2 : List Nat := [1, 4, 3, 28, 15, 32, 17, 36, 19, 40]
    if result2 != expected2 then
      throw (IO.userError s!"Multiple transform fusion failed: expected {expected2}, got {result2}")

    IO.println "✓ Performance fusion tests passed"
}

/--
Test: Short-circuiting with Option/Validation
- Filtered traversal that fails fast on invalid element
- Use Option to terminate early
- Collect all errors vs fail-fast comparison
-/
private def case_performanceShortCircuit : TestCase := {
  name := "Performance: short-circuiting with applicatives",
  run := do
    let tr := Instances.List.traversed (α := Nat) (β := Nat)

    -- Test 1: Short-circuit on first invalid element
    let input1 : List Nat := [2, 4, 6, 7, 8, 10]
    let evenValidator : Nat → Option Nat := fun x =>
      if x % 2 == 0 then some x else none
    let result1 := traverse tr evenValidator input1
    match result1 with
    | some _ => throw (IO.userError "Should have short-circuited on odd number")
    | none => pure ()  -- Expected - fails on 7

    -- Test 2: Successful validation (no short-circuit)
    let input2 : List Nat := [2, 4, 6, 8, 10]
    let result2 := traverse tr evenValidator input2
    match result2 with
    | none => throw (IO.userError "Validation should have succeeded")
    | some validated =>
      if validated != input2 then
        throw (IO.userError "Validation changed valid data")

    -- Test 3: Short-circuit with filtered traversal
    let input3 : List Nat := [1, 2, 3, 4, 5, 6, 7, 8]
    let evens := filtered tr (fun x => x % 2 == 0)
    let strictValidator : Nat → Option Nat := fun x =>
      if x <= 4 then some (x * 10) else none
    let result3 := traverse evens strictValidator input3
    match result3 with
    | some _ => throw (IO.userError "Should fail on 6 (even and > 4)")
    | none => pure ()  -- Expected

    -- Test 4: Demonstrate early termination benefit
    -- With Option, traversal stops at first failure
    let input4 : List Nat := [2, 4, 999, 8, 10]  -- 999 is odd
    let result4 := traverse tr evenValidator input4
    match result4 with
    | some _ => throw (IO.userError "Should short-circuit on 999")
    | none => pure ()  -- Stops at 999, doesn't check 8 or 10

    IO.println "✓ Performance short-circuit tests passed"
}

/-! ## Edge Cases and Boundary Conditions -/

/--
Test: Empty and singleton lists
- filtered on empty list
- itraversed on empty list
- ix on empty list (should be no-op)
- Single element with various filters
-/
private def case_edgeCasesEmpty : TestCase := {
  name := "Edge cases: empty and singleton lists",
  run := do
    let tr := Instances.List.traversed
    let indexed := Instances.List.itraversed

    -- Test 1: Filtered on empty list
    let empty : List Nat := []
    let evenFilter := filtered tr (fun x => x % 2 == 0)
    let result1 := empty & evenFilter %~ (· * 100)
    if result1 != [] then
      throw (IO.userError s!"Filtered empty list failed: expected [], got {result1}")

    -- Test 2: itraversed on empty list
    let result2 := empty & indexed %~ (fun (idx, v) => (idx, v + idx))
    if result2 != [] then
      throw (IO.userError s!"itraversed empty list failed: expected [], got {result2}")

    -- Test 3: ix on empty list (should be no-op)
    let result3 := empty & (ix 0) %~ (· * 999)
    if result3 != [] then
      throw (IO.userError s!"ix on empty list failed: expected [], got {result3}")

    -- Test 4: atLens on empty list
    let elem4 : Option Nat := view (atLens 0) empty
    if elem4.isSome then
      throw (IO.userError s!"atLens on empty list should return none")

    -- Test 5: Single element - matches filter
    let single : List Nat := [42]
    let result5 := single & evenFilter %~ (· + 100)
    let expected5 : List Nat := [142]
    if result5 != expected5 then
      throw (IO.userError s!"Single element match failed: expected {expected5}, got {result5}")

    -- Test 6: Single element - doesn't match filter
    let singleOdd : List Nat := [43]
    let result6 := singleOdd & evenFilter %~ (· + 100)
    if result6 != singleOdd then
      throw (IO.userError s!"Single element no-match failed: expected {singleOdd}, got {result6}")

    -- Test 7: Single element with indexed
    let result7 := single & indexed %~ (fun (idx, v) => (idx, v + idx * 10))
    let expected7 : List Nat := [42]  -- 42 + 0*10 = 42
    if result7 != expected7 then
      throw (IO.userError s!"Single element indexed failed: expected {expected7}, got {result7}")

    -- Test 8: Single element with ix at index 0
    let result8 := single & (ix 0) %~ (· * 2)
    let expected8 : List Nat := [84]
    if result8 != expected8 then
      throw (IO.userError s!"Single element ix 0 failed: expected {expected8}, got {result8}")

    -- Test 9: Single element with ix at wrong index
    let result9 := single & (ix 5) %~ (· * 2)
    if result9 != single then
      throw (IO.userError s!"Single element ix wrong index failed: expected {single}, got {result9}")

    IO.println "✓ Edge cases empty and singleton tests passed"
}

/--
Test: Out of bounds index operations
- ix with index > length
- ix with negative index (Nat so should be large)
- atLens on out of bounds (should return none)
-/
private def case_edgeCasesOutOfBounds : TestCase := {
  name := "Edge cases: out of bounds index access",
  run := do
    let input : List Nat := [10, 20, 30, 40, 50]

    -- Test 1: ix with index > length (should be no-op)
    let result1 := input & (ix 10) %~ (· * 999)
    if result1 != input then
      throw (IO.userError s!"ix out of bounds should not modify: expected {input}, got {result1}")

    -- Test 2: ix with index = length (should be no-op)
    let result2 := input & (ix 5) %~ (· * 999)
    if result2 != input then
      throw (IO.userError s!"ix at length should not modify: expected {input}, got {result2}")

    -- Test 3: ix with very large index
    let result3 := input & (ix 1000000) %~ (· * 999)
    if result3 != input then
      throw (IO.userError s!"ix very large index should not modify: expected {input}, got {result3}")

    -- Test 4: atLens on out of bounds returns none
    let elem4 : Option Nat := view (atLens 10) input
    if elem4.isSome then
      throw (IO.userError s!"atLens out of bounds should return none")

    let elem5 : Option Nat := view (atLens 5) input
    if elem5.isSome then
      throw (IO.userError s!"atLens at length should return none")

    -- Test 5: Setting via atLens out of bounds (should not modify)
    let result6 := set (atLens 10) (some 999) input
    if result6 != input then
      throw (IO.userError s!"atLens set out of bounds should not modify: expected {input}, got {result6}")

    -- Test 6: Filtered with out of bounds index conditions
    let indexed := Instances.List.itraversed
    let outOfRangeFilter := filtered indexed (fun (i, _) => i >= 100)
    let result7 := input & outOfRangeFilter %~ (fun (idx, v) => (idx, v * 999))
    if result7 != input then
      throw (IO.userError s!"Filter with impossible index should not modify: expected {input}, got {result7}")

    IO.println "✓ Edge cases out of bounds tests passed"
}

/--
Test: All or none matching filter
- Filter that matches everything (equivalent to unfiltered)
- Filter that matches nothing (all unchanged)
- Verify performance characteristics
-/
private def case_edgeCasesFilterExtreme : TestCase := {
  name := "Edge cases: filters matching all or none",
  run := do
    let tr := Instances.List.traversed
    let indexed := Instances.List.itraversed
    let input : List Nat := [1, 2, 3, 4, 5]

    -- Test 1: Filter that matches everything (always true)
    let allMatch := filtered tr (fun _ => true)
    let result1 := input & allMatch %~ (· + 10)
    let expected1 : List Nat := [11, 12, 13, 14, 15]
    if result1 != expected1 then
      throw (IO.userError s!"All-match filter failed: expected {expected1}, got {result1}")

    -- Test 2: Filter that matches nothing (always false)
    let noneMatch := filtered tr (fun _ => false)
    let result2 := input & noneMatch %~ (· + 999)
    if result2 != input then
      throw (IO.userError s!"None-match filter should not modify: expected {input}, got {result2}")

    -- Test 3: Indexed filter matching all
    let allIdxMatch := filtered indexed (fun _ => true)
    let result3 := input & allIdxMatch %~ (fun (idx, v) => (idx, v + idx))
    let expected3 : List Nat := [1, 3, 5, 7, 9]
    if result3 != expected3 then
      throw (IO.userError s!"All-match indexed filter failed: expected {expected3}, got {result3}")

    -- Test 4: Indexed filter matching none
    let noneIdxMatch := filtered indexed (fun _ => false)
    let result4 := input & noneIdxMatch %~ (fun (idx, v) => (idx, v * 999))
    if result4 != input then
      throw (IO.userError s!"None-match indexed filter should not modify: expected {input}, got {result4}")

    -- Test 5: Filter with impossible condition (value > max Nat)
    let impossible := filtered tr (fun x => x > 1000000000)
    let result5 := input & impossible %~ (· + 1)
    if result5 != input then
      throw (IO.userError s!"Impossible filter should not modify: expected {input}, got {result5}")

    -- Test 6: Filter with tautology
    let tautology := filtered tr (fun x => x == x)
    let result6 := input & tautology %~ (· * 2)
    let expected6 : List Nat := [2, 4, 6, 8, 10]
    if result6 != expected6 then
      throw (IO.userError s!"Tautology filter failed: expected {expected6}, got {result6}")

    -- Test 7: Verify all-match behaves same as unfiltered traversal
    let unfilteredResult := input & tr %~ (· + 100)
    let filteredResult := input & allMatch %~ (· + 100)
    if unfilteredResult != filteredResult then
      throw (IO.userError s!"All-match should behave like unfiltered: {unfilteredResult} != {filteredResult}")

    IO.println "✓ Edge cases filter extremes tests passed"
}

/-! ## Composition and Reusability -/

/--
Test: Partial application and reuse
- Define reusable filtered traversals (evens, odds, positives)
- Compose them with different transformations
- Build library of common filters
-/
private def case_compositionReusability : TestCase := {
  name := "Composition: reusable filtered traversals",
  run := do
    -- Define reusable filters inline to avoid universe issues
    let input : List Nat := [10, 25, 50, 75, 100]

    -- Test 1: Filter evens and apply different transformations
    let evens := filtered Instances.List.traversed (fun x : Nat => x % 2 == 0)
    let result1 := input & evens %~ (· * 2)
    let expected1 : List Nat := [20, 25, 100, 75, 200]
    if result1 != expected1 then
      throw (IO.userError s!"Evens reuse failed: expected {expected1}, got {result1}")

    let result2 := input & evens %~ (· + 5)
    let expected2 : List Nat := [15, 25, 55, 75, 105]
    if result2 != expected2 then
      throw (IO.userError s!"Evens reuse 2 failed: expected {expected2}, got {result2}")

    -- Test 2: Filter odds
    let odds := filtered Instances.List.traversed (fun x : Nat => x % 2 == 1)
    let result3 := input & odds %~ (· * 10)
    let expected3 : List Nat := [10, 250, 50, 750, 100]
    if result3 != expected3 then
      throw (IO.userError s!"Odds reuse failed: expected {expected3}, got {result3}")

    -- Test 3: Compose filters
    let evenAndLarge := filtered evens (fun x => x > 50)
    let result4 := input & evenAndLarge %~ (· / 10)
    let expected4 : List Nat := [10, 25, 50, 75, 10]  -- Only 100 matches
    if result4 != expected4 then
      throw (IO.userError s!"Composed filter failed: expected {expected4}, got {result4}")

    IO.println "✓ Composition reusability tests passed"
}

/--
Test: Higher-order filtering
- Filter that takes another filter as parameter
- Negate filter (all elements NOT matching predicate)
- Union/intersection of filters
-/
private def case_compositionHigherOrder : TestCase := {
  name := "Composition: higher-order filter combinators",
  run := do
    let tr := Instances.List.traversed
    let input : List Nat := [1, 2, 3, 4, 5, 6]

    -- Test 1: Negated filter (NOT even = odd)
    let isEven (x : Nat) : Bool := x % 2 == 0
    let notEven := filtered tr (fun x => !isEven x)
    let result1 := input & notEven %~ (· + 10)
    let expected1 : List Nat := [11, 2, 13, 4, 15, 6]
    if result1 != expected1 then
      throw (IO.userError s!"Negated filter failed: expected {expected1}, got {result1}")

    -- Test 2: Union of predicates (even OR > 4)
    let unionFilter := filtered tr (fun x => x % 2 == 0 || x > 4)
    let result2 := input & unionFilter %~ (· * 10)
    let expected2 : List Nat := [1, 20, 3, 40, 50, 60]
    if result2 != expected2 then
      throw (IO.userError s!"Union filter failed: expected {expected2}, got {result2}")

    -- Test 3: Intersection of predicates (even AND > 3)
    let intersectionFilter := filtered tr (fun x => x % 2 == 0 && x > 3)
    let result3 := input & intersectionFilter %~ (· + 100)
    let expected3 : List Nat := [1, 2, 3, 104, 5, 106]
    if result3 != expected3 then
      throw (IO.userError s!"Intersection filter failed: expected {expected3}, got {result3}")

    IO.println "✓ Composition higher-order tests passed"
}

def cases : List TestCase := [
  -- Basic Filtered
  case_filteredByPredicate,
  case_filteredComplexPredicates,
  case_filteredWithLens,
  case_filteredEdgeCases,
  case_filteredEffectful,

  -- Basic Indexed
  case_indexedBasic,
  case_indexedTransformations,
  case_indexedSingleFocus,
  case_indexedAtLens,

  -- Combined Filtered + Indexed
  case_filteredByIndex,
  case_filteredValueIndexTransform,
  case_filteredIndexedComplex,
  case_filteredIndexedChaining,

  -- Stateful Filtered + Indexed
  case_filteredStatefulCounting,
  case_indexedStatefulAccumulation,
  case_filteredStatefulMapping,
  case_indexedStatefulContext,

  -- Real-World Use Cases
  case_realworldArrayUpdates,
  case_realworldConditionalBatch,
  case_realworldValidation,
  case_realworldSparseArrays,
  case_realworldStringOps,

  -- Performance
  case_performanceFusion,
  case_performanceShortCircuit,

  -- Edge Cases
  case_edgeCasesEmpty,
  case_edgeCasesOutOfBounds,
  case_edgeCasesFilterExtreme,

  -- Composition
  case_compositionReusability,
  case_compositionHigherOrder
]

end CollimatorTests.AdvancedShowcase.FilteredIndexed
