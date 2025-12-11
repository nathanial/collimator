import Batteries
import Collimator.Optics
import Collimator.Combinators
import Collimator.Instances
import Collimator.Operators
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
open scoped Collimator.Operators

/-! ## Empty Structure Tests -/

/--
Test traversal over empty list preserves structure.
-/
private def case_empty_list_traversal : TestCase := {
  name := "Edge: Traversal over empty list returns empty list",
  run := do
    let tr : Traversal' (List Int) Int := Traversal.eachList
    let result := ([] : List Int) & tr %~ (· + 100)
    result ≡ ([] : List Int)
}

/--
Test fold over empty list returns empty.
-/
private def case_empty_list_fold : TestCase := {
  name := "Edge: Fold over empty list returns empty",
  run := do
    let tr : Traversal' (List Int) Int := Traversal.eachList
    let result := ([] : List Int) ^.. tr
    result ≡ ([] : List Int)
}

/--
Test traversal over Option.none preserves none.
-/
private def case_none_traversal : TestCase := {
  name := "Edge: Traversal over none returns none",
  run := do
    let tr : Traversal' (Option Int) Int := Traversal.eachOption
    let result := (none : Option Int) & tr %~ (· * 2)
    result ≡ (none : Option Int)
}

/--
Test prism preview on non-matching value.
-/
private def case_prism_no_match : TestCase := {
  name := "Edge: Prism preview returns none for non-matching",
  run := do
    let p : Prism' (Sum Int String) Int := Collimator.Instances.Sum.left' (α := Int) (β := String)
    let result := Sum.inr "not an int" ^? p
    result ≡ (none : Option Int)
}

/--
Test affine traversal with no focus.
-/
private def case_affine_no_focus : TestCase := {
  name := "Edge: Affine traversal with no focus leaves unchanged",
  run := do
    let prism : Prism' (Option Int) Int := Collimator.Instances.Option.somePrism' Int
    let aff : AffineTraversal' (Option Int) Int := AffineTraversalOps.ofPrism prism
    let result := (none : Option Int) & aff .~ 999
    result ≡ (none : Option Int)
}

/-! ## Single Element Tests -/

/--
Test traversal over single element list.
-/
private def case_single_element_list : TestCase := {
  name := "Edge: Single element list traversal",
  run := do
    let tr : Traversal' (List Int) Int := Traversal.eachList
    let result := [42] & tr %~ (· + 1)
    result ≡ [43]
}

/--
Test traversal over Some value.
-/
private def case_some_traversal : TestCase := {
  name := "Edge: Some value traversal",
  run := do
    let tr : Traversal' (Option Int) Int := Traversal.eachOption
    let result := some 7 & tr %~ (· * 3)
    result ≡ (some 21)
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

    (nested ^. composed) ≡ 1
    (nested & composed .~ 99) ≡ ((((99, 2), 3), 4))
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

    (nested ^. composed) ≡ 1
    (nested & composed .~ 42) ≡ (((((42, 2), 3), 4), 5))
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

    let result := pair & composed %~ (· + 10)
    result ≡ (([11, 12, 13], "hello"))
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

    let result := pairs & composed %~ (· * 2)
    result ≡ ([(2, "a"), (4, "b"), (6, "c")])
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

    let preview1 := pair1 ^? composed
    preview1 ≡? 42

    let preview2 := pair2 ^? composed
    preview2 ≡ (none : Option Int)

    let set1 := pair1 & composed .~ 99
    set1 ≡ ((some 99, "test"))
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

    let result := largeList & tr %~ (· + 1)

    result.length ≡ 1000
    result.head? ≡? 1
    result.getLast? ≡? 1000
}

/--
Test fold to list over large list.
-/
private def case_large_list_fold : TestCase := {
  name := "Stress: Large list fold to list",
  run := do
    let largeList : List Int := (List.range 500).map (Int.ofNat ·)
    let tr : Traversal' (List Int) Int := Traversal.eachList

    let result := largeList ^.. tr

    result.length ≡ 500
    result ≡ largeList
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
    let result := nestedList & composed %~ (· * 10)

    result ≡ ([[10, 20], [30, 40, 50], [60]])
}

/-! ## Type Boundary Tests -/

/--
Test identity lens preserves all values.
-/
private def case_identity_lens : TestCase := {
  name := "Edge: Identity lens",
  run := do
    let idLens : Lens' Int Int := lens' id (fun _ x => x)

    (42 ^. idLens) ≡ 42
    (42 & idLens .~ 99) ≡ 99
    (42 & idLens %~ (· + 8)) ≡ 50
}

/--
Test constant lens (always returns same value).
-/
private def case_constant_lens : TestCase := {
  name := "Edge: Constant lens behavior",
  run := do
    let constLens : Lens' (Int × Int) Int := const 0

    let pair : (Int × Int) := (10, 20)

    (pair ^. constLens) ≡ 0
    (pair & constLens .~ 999) ≡ pair
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
    result ≡ (none : Option (List Int))
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
    result ≡ (some [2, 3, 4])
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
    result ≡ (some [])
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

    first ≡? 10
    middle ≡? 30
    last ≡? 50
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

    tooLarge ≡ (none : Option Int)
    exactlyTooLarge ≡ (none : Option Int)
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
