import Batteries
import Collimator.Optics
import Collimator.Combinators
import Collimator.Instances
import CollimatorTests.Framework

/-!
# Edge Case Tests for Collimator Optics

Tests for edge cases, boundary conditions, and stress tests.
-/

namespace CollimatorTests.EdgeCases

open Collimator
open Collimator.Core
open Collimator.Concrete
open Collimator.Combinators
open Collimator.Instances
open CollimatorTests

/-! ## Empty Structure Tests -/

/--
Test traversal over empty list preserves structure.
-/
private def case_empty_list_traversal : TestCase := {
  name := "Edge: Traversal over empty list returns empty list",
  run := do
    let tr : Traversal' (List Int) Int := Traversal.eachList
    let result := Traversal.over' tr (· + 100) []
    ensureEq "Empty list traversal" ([] : List Int) result
}

/--
Test fold over empty list returns empty.
-/
private def case_empty_list_fold : TestCase := {
  name := "Edge: Fold over empty list returns empty",
  run := do
    let tr : Traversal' (List Int) Int := Traversal.eachList
    let result := Fold.toListTraversal tr []
    ensureEq "Empty list fold" ([] : List Int) result
}

/--
Test traversal over Option.none preserves none.
-/
private def case_none_traversal : TestCase := {
  name := "Edge: Traversal over none returns none",
  run := do
    let tr : Traversal' (Option Int) Int := Traversal.eachOption
    let result := Traversal.over' tr (· * 2) none
    ensureEq "None traversal" (none : Option Int) result
}

/--
Test prism preview on non-matching value.
-/
private def case_prism_no_match : TestCase := {
  name := "Edge: Prism preview returns none for non-matching",
  run := do
    let p : Prism' (Sum Int String) Int := Collimator.Instances.Sum.left' (α := Int) (β := String)
    let result := preview' p (Sum.inr "not an int")
    ensureEq "Prism no match" (none : Option Int) result
}

/--
Test affine traversal with no focus.
-/
private def case_affine_no_focus : TestCase := {
  name := "Edge: Affine traversal with no focus leaves unchanged",
  run := do
    let prism : Prism' (Option Int) Int := Collimator.Instances.Option.somePrism' Int
    let aff : AffineTraversal' (Option Int) Int := AffineTraversalOps.ofPrism prism
    let result := AffineTraversalOps.set aff 999 none
    ensureEq "Affine no focus" (none : Option Int) result
}

/-! ## Single Element Tests -/

/--
Test traversal over single element list.
-/
private def case_single_element_list : TestCase := {
  name := "Edge: Single element list traversal",
  run := do
    let tr : Traversal' (List Int) Int := Traversal.eachList
    let result := Traversal.over' tr (· + 1) [42]
    ensureEq "Single element" [43] result
}

/--
Test traversal over Some value.
-/
private def case_some_traversal : TestCase := {
  name := "Edge: Some value traversal",
  run := do
    let tr : Traversal' (Option Int) Int := Traversal.eachOption
    let result := Traversal.over' tr (· * 3) (some 7)
    ensureEq "Some traversal" (some 21) result
}

/-! ## Deep Composition Tests -/

/--
Test 3-level lens composition.
-/
private def case_three_level_lens : TestCase := {
  name := "Edge: 3-level lens composition",
  run := do
    let nested : (((Int × Int) × Int) × Int) := (((1, 2), 3), 4)

    let l1 : Lens' ((((Int × Int) × Int) × Int)) (((Int × Int) × Int)) := _1
    let l2 : Lens' (((Int × Int) × Int)) ((Int × Int)) := _1
    let l3 : Lens' ((Int × Int)) Int := _1

    let composed : Lens' ((((Int × Int) × Int) × Int)) Int := l1 ∘ l2 ∘ l3

    ensureEq "3-level view" 1 (view' composed nested)
    ensureEq "3-level set" ((((99, 2), 3), 4)) (set' composed 99 nested)
}

/--
Test 5-level lens composition.
-/
private def case_five_level_lens : TestCase := {
  name := "Edge: 5-level lens composition",
  run := do
    let nested : ((((Int × Int) × Int) × Int) × Int) := ((((1, 2), 3), 4), 5)

    let l1 : Lens' (((((Int × Int) × Int) × Int) × Int)) ((((Int × Int) × Int) × Int)) := _1
    let l2 : Lens' ((((Int × Int) × Int) × Int)) (((Int × Int) × Int)) := _1
    let l3 : Lens' (((Int × Int) × Int)) ((Int × Int)) := _1
    let l4 : Lens' ((Int × Int)) Int := _1

    let composed : Lens' (((((Int × Int) × Int) × Int) × Int)) Int := l1 ∘ l2 ∘ l3 ∘ l4

    ensureEq "5-level view" 1 (view' composed nested)
    ensureEq "5-level set" (((((42, 2), 3), 4), 5)) (set' composed 42 nested)
}

/--
Test mixed optic composition: Lens ∘ Traversal.
-/
private def case_lens_traversal_composition : TestCase := {
  name := "Edge: Lens ∘ Traversal composition",
  run := do
    let pair : (List Int × String) := ([1, 2, 3], "hello")

    let lensToList : Lens' (List Int × String) (List Int) := _1
    let traverseList : Traversal' (List Int) Int := Traversal.eachList

    let composed : Traversal' (List Int × String) Int := lensToList ∘ traverseList

    let result := Traversal.over' composed (· + 10) pair
    ensureEq "Lens ∘ Traversal" (([11, 12, 13], "hello")) result
}

/--
Test mixed optic composition: Traversal ∘ Lens.
-/
private def case_traversal_lens_composition : TestCase := {
  name := "Edge: Traversal ∘ Lens composition",
  run := do
    let pairs : List (Int × String) := [(1, "a"), (2, "b"), (3, "c")]

    let traverseList : Traversal' (List (Int × String)) (Int × String) := Traversal.eachList
    let lensToFirst : Lens' (Int × String) Int := _1

    let composed : Traversal' (List (Int × String)) Int := traverseList ∘ lensToFirst

    let result := Traversal.over' composed (· * 2) pairs
    ensureEq "Traversal ∘ Lens" ([(2, "a"), (4, "b"), (6, "c")]) result
}

/--
Test Lens ∘ Prism composition creating AffineTraversal.
-/
private def case_lens_prism_composition : TestCase := {
  name := "Edge: Lens ∘ Prism composition",
  run := do
    let pair1 : (Option Int × String) := (some 42, "test")
    let pair2 : (Option Int × String) := (none, "test")

    let lensToOpt : Lens' (Option Int × String) (Option Int) := _1
    let prismToSome : Prism' (Option Int) Int := Collimator.Instances.Option.somePrism' Int

    let composed : AffineTraversal' (Option Int × String) Int := lensToOpt ∘ prismToSome

    let preview1 := AffineTraversalOps.preview' composed pair1
    ensureEq "Lens ∘ Prism preview some" (some 42) preview1

    let preview2 := AffineTraversalOps.preview' composed pair2
    ensureEq "Lens ∘ Prism preview none" (none : Option Int) preview2

    let set1 := AffineTraversalOps.set composed 99 pair1
    ensureEq "Lens ∘ Prism set some" ((some 99, "test")) set1
}

/-! ## Large Structure Tests -/

/--
Test traversal over large list (1000 elements).
-/
private def case_large_list_traversal : TestCase := {
  name := "Stress: Large list (1000 elements) traversal",
  run := do
    let largeList : List Int := (List.range 1000).map (Int.ofNat ·)
    let tr : Traversal' (List Int) Int := Traversal.eachList

    let result := Traversal.over' tr (· + 1) largeList

    ensure (result.length == 1000) "Large list same length"
    ensure (result.head? == some 1) "Large list first element"
    ensure (result.getLast? == some 1000) "Large list last element"
}

/--
Test fold to list over large list.
-/
private def case_large_list_fold : TestCase := {
  name := "Stress: Large list fold to list",
  run := do
    let largeList : List Int := (List.range 500).map (Int.ofNat ·)
    let tr : Traversal' (List Int) Int := Traversal.eachList

    let result := Fold.toListTraversal tr largeList

    ensure (result.length == 500) "Fold preserves length"
    ensure (result == largeList) "Fold preserves elements"
}

/--
Test nested list traversal (List of Lists).
-/
private def case_nested_list_traversal : TestCase := {
  name := "Stress: Nested list traversal",
  run := do
    let nestedList : List (List Int) := [[1, 2], [3, 4, 5], [6]]

    let outerTr : Traversal' (List (List Int)) (List Int) := Traversal.eachList
    let innerTr : Traversal' (List Int) Int := Traversal.eachList

    let composed : Traversal' (List (List Int)) Int := outerTr ∘ innerTr
    let result := Traversal.over' composed (· * 10) nestedList

    ensureEq "Nested traversal" ([[10, 20], [30, 40, 50], [60]]) result
}

/-! ## Type Boundary Tests -/

/--
Test identity lens preserves all values.
-/
private def case_identity_lens : TestCase := {
  name := "Edge: Identity lens",
  run := do
    let idLens : Lens' Int Int := lens' id (fun _ x => x)

    ensureEq "Id lens view" 42 (view' idLens 42)
    ensureEq "Id lens set" 99 (set' idLens 99 42)
    ensureEq "Id lens over" 50 (over' idLens (· + 8) 42)
}

/--
Test constant lens (always returns same value).
-/
private def case_constant_lens : TestCase := {
  name := "Edge: Constant lens behavior",
  run := do
    let constLens : Lens' (Int × Int) Int := const 0

    let pair : (Int × Int) := (10, 20)

    ensureEq "Const lens view" 0 (view' constLens pair)
    ensureEq "Const lens set" pair (set' constLens 999 pair)
}

/-! ## Effect Edge Cases -/

/--
Test traverse with always-failing effect.
-/
private def case_traverse_always_fails : TestCase := {
  name := "Edge: Traverse with always-failing effect",
  run := do
    let tr : Traversal' (List Int) Int := Traversal.eachList
    let alwaysFail : Int → Option Int := fun _ => none

    let result := Traversal.traverse' tr alwaysFail [1, 2, 3]
    ensureEq "Always fail traverse" (none : Option (List Int)) result
}

/--
Test traverse with always-succeeding effect.
-/
private def case_traverse_always_succeeds : TestCase := {
  name := "Edge: Traverse with always-succeeding effect",
  run := do
    let tr : Traversal' (List Int) Int := Traversal.eachList
    let alwaysSucceed : Int → Option Int := fun x => some (x + 1)

    let result := Traversal.traverse' tr alwaysSucceed [1, 2, 3]
    ensureEq "Always succeed traverse" (some [2, 3, 4]) result
}

/--
Test traverse over empty with failing effect still succeeds.
-/
private def case_traverse_empty_with_fail : TestCase := {
  name := "Edge: Traverse empty list with failing effect succeeds",
  run := do
    let tr : Traversal' (List Int) Int := Traversal.eachList
    let alwaysFail : Int → Option Int := fun _ => none

    let result := Traversal.traverse' tr alwaysFail []
    ensureEq "Empty with fail" (some []) result
}

/-! ## Index Boundary Tests -/

/--
Test list index access at valid indices.
-/
private def case_list_index_valid : TestCase := {
  name := "Edge: List index access at valid indices",
  run := do
    let xs := [10, 20, 30, 40, 50]

    let first := xs.get? 0
    let middle := xs.get? 2
    let last := xs.get? 4

    ensureEq "Index 0" (some 10) first
    ensureEq "Index 2" (some 30) middle
    ensureEq "Index 4" (some 50) last
}

/--
Test list index access at invalid indices.
-/
private def case_list_index_invalid : TestCase := {
  name := "Edge: List index access at invalid indices",
  run := do
    let xs := [10, 20, 30]

    let tooLarge := xs.get? 10
    let exactlyTooLarge := xs.get? 3

    ensureEq "Index 10 invalid" (none : Option Int) tooLarge
    ensureEq "Index 3 invalid" (none : Option Int) exactlyTooLarge
}

/-! ## All Test Cases -/

def cases : List TestCase :=
  [ case_empty_list_traversal
  , case_empty_list_fold
  , case_none_traversal
  , case_prism_no_match
  , case_affine_no_focus
  , case_single_element_list
  , case_some_traversal
  , case_three_level_lens
  , case_five_level_lens
  , case_lens_traversal_composition
  , case_traversal_lens_composition
  , case_lens_prism_composition
  , case_large_list_traversal
  , case_large_list_fold
  , case_nested_list_traversal
  , case_identity_lens
  , case_constant_lens
  , case_traverse_always_fails
  , case_traverse_always_succeeds
  , case_traverse_empty_with_fail
  , case_list_index_valid
  , case_list_index_invalid
  ]

end CollimatorTests.EdgeCases
