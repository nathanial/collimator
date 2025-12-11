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

testSuite "Edge Cases"

/-! ## Empty Structure Tests -/

test "Edge: Traversal over empty list returns empty list" := do
  let tr : Traversal' (List Int) Int := Traversal.eachList
  let result := ([] : List Int) & tr %~ (· + 100)
  result ≡ ([] : List Int)

test "Edge: Fold over empty list returns empty" := do
  let tr : Traversal' (List Int) Int := Traversal.eachList
  let result := ([] : List Int) ^.. tr
  result ≡ ([] : List Int)

test "Edge: Traversal over none returns none" := do
  let tr : Traversal' (Option Int) Int := Traversal.eachOption
  let result := (none : Option Int) & tr %~ (· * 2)
  result ≡ (none : Option Int)

test "Edge: Prism preview returns none for non-matching" := do
  let p : Prism' (Sum Int String) Int := Collimator.Instances.Sum.left' (α := Int) (β := String)
  let result := Sum.inr "not an int" ^? p
  result ≡ (none : Option Int)

test "Edge: Affine traversal with no focus leaves unchanged" := do
  let prism : Prism' (Option Int) Int := Collimator.Instances.Option.somePrism' Int
  let aff : AffineTraversal' (Option Int) Int := AffineTraversalOps.ofPrism prism
  let result := (none : Option Int) & aff .~ 999
  result ≡ (none : Option Int)

/-! ## Single Element Tests -/

test "Edge: Single element list traversal" := do
  let tr : Traversal' (List Int) Int := Traversal.eachList
  let result := [42] & tr %~ (· + 1)
  result ≡ [43]

test "Edge: Some value traversal" := do
  let tr : Traversal' (Option Int) Int := Traversal.eachOption
  let result := some 7 & tr %~ (· * 3)
  result ≡ (some 21)

/-! ## Deep Composition Tests -/

test "Edge: 3-level lens composition" := do
  let nested : (((Int × Int) × Int) × Int) := (((1, 2), 3), 4)

  let l1 : Lens' ((((Int × Int) × Int) × Int)) (((Int × Int) × Int)) := _1
  let l2 : Lens' (((Int × Int) × Int)) ((Int × Int)) := _1
  let l3 : Lens' ((Int × Int)) Int := _1

  let composed : Lens' ((((Int × Int) × Int) × Int)) Int := l1 ∘ l2 ∘ l3

  (nested ^. composed) ≡ 1
  (nested & composed .~ 99) ≡ ((((99, 2), 3), 4))

test "Edge: 5-level lens composition" := do
  let nested : ((((Int × Int) × Int) × Int) × Int) := ((((1, 2), 3), 4), 5)

  let l1 : Lens' (((((Int × Int) × Int) × Int) × Int)) ((((Int × Int) × Int) × Int)) := _1
  let l2 : Lens' ((((Int × Int) × Int) × Int)) (((Int × Int) × Int)) := _1
  let l3 : Lens' (((Int × Int) × Int)) ((Int × Int)) := _1
  let l4 : Lens' ((Int × Int)) Int := _1

  let composed : Lens' (((((Int × Int) × Int) × Int) × Int)) Int := l1 ∘ l2 ∘ l3 ∘ l4

  (nested ^. composed) ≡ 1
  (nested & composed .~ 42) ≡ (((((42, 2), 3), 4), 5))

test "Edge: Lens ∘ Traversal composition" := do
  let pair : (List Int × String) := ([1, 2, 3], "hello")

  let lensToList : Lens' (List Int × String) (List Int) := _1
  let traverseList : Traversal' (List Int) Int := Traversal.eachList

  let composed : Traversal' (List Int × String) Int := lensToList ∘ traverseList

  let result := pair & composed %~ (· + 10)
  result ≡ (([11, 12, 13], "hello"))

test "Edge: Traversal ∘ Lens composition" := do
  let pairs : List (Int × String) := [(1, "a"), (2, "b"), (3, "c")]

  let traverseList : Traversal' (List (Int × String)) (Int × String) := Traversal.eachList
  let lensToFirst : Lens' (Int × String) Int := _1

  let composed : Traversal' (List (Int × String)) Int := traverseList ∘ lensToFirst

  let result := pairs & composed %~ (· * 2)
  result ≡ ([(2, "a"), (4, "b"), (6, "c")])

test "Edge: Lens ∘ Prism composition" := do
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

/-! ## Large Structure Tests -/

test "Stress: Large list (1000 elements) traversal" := do
  let largeList : List Int := (List.range 1000).map (Int.ofNat ·)
  let tr : Traversal' (List Int) Int := Traversal.eachList

  let result := largeList & tr %~ (· + 1)

  result.length ≡ 1000
  result.head? ≡? 1
  result.getLast? ≡? 1000

test "Stress: Large list fold to list" := do
  let largeList : List Int := (List.range 500).map (Int.ofNat ·)
  let tr : Traversal' (List Int) Int := Traversal.eachList

  let result := largeList ^.. tr

  result.length ≡ 500
  result ≡ largeList

test "Stress: Nested list traversal" := do
  let nestedList : List (List Int) := [[1, 2], [3, 4, 5], [6]]

  let outerTr : Traversal' (List (List Int)) (List Int) := Traversal.eachList
  let innerTr : Traversal' (List Int) Int := Traversal.eachList

  let composed : Traversal' (List (List Int)) Int := outerTr ∘ innerTr
  let result := nestedList & composed %~ (· * 10)

  result ≡ ([[10, 20], [30, 40, 50], [60]])

/-! ## Type Boundary Tests -/

test "Edge: Identity lens" := do
  let idLens : Lens' Int Int := lens' id (fun _ x => x)

  (42 ^. idLens) ≡ 42
  (42 & idLens .~ 99) ≡ 99
  (42 & idLens %~ (· + 8)) ≡ 50

test "Edge: Constant lens behavior" := do
  let constLens : Lens' (Int × Int) Int := const 0

  let pair : (Int × Int) := (10, 20)

  (pair ^. constLens) ≡ 0
  (pair & constLens .~ 999) ≡ pair

/-! ## Effect Edge Cases -/

test "Edge: Traverse with always-failing effect" := do
  let tr : Traversal' (List Int) Int := Traversal.eachList
  let alwaysFail : Int → Option Int := fun _ => none

  let result := Traversal.traverse' tr alwaysFail [1, 2, 3]
  result ≡ (none : Option (List Int))

test "Edge: Traverse with always-succeeding effect" := do
  let tr : Traversal' (List Int) Int := Traversal.eachList
  let alwaysSucceed : Int → Option Int := fun x => some (x + 1)

  let result := Traversal.traverse' tr alwaysSucceed [1, 2, 3]
  result ≡ (some [2, 3, 4])

test "Edge: Traverse empty list with failing effect succeeds" := do
  let tr : Traversal' (List Int) Int := Traversal.eachList
  let alwaysFail : Int → Option Int := fun _ => none

  let result := Traversal.traverse' tr alwaysFail []
  result ≡ (some [])

/-! ## Index Boundary Tests -/

test "Edge: List index access at valid indices" := do
  let xs := [10, 20, 30, 40, 50]

  let first := xs.get? 0
  let middle := xs.get? 2
  let last := xs.get? 4

  first ≡? 10
  middle ≡? 30
  last ≡? 50

test "Edge: List index access at invalid indices" := do
  let xs := [10, 20, 30]

  let tooLarge := xs.get? 10
  let exactlyTooLarge := xs.get? 3

  tooLarge ≡ (none : Option Int)
  exactlyTooLarge ≡ (none : Option Int)

#generate_tests

end CollimatorTests.EdgeCases
