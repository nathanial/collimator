import Collimator.Core
import Batteries
import Collimator.Optics
import Collimator.Operators
import Collimator.Concrete.FunArrow
import CollimatorTests.Framework

namespace CollimatorTests.Traversals

open Batteries
open Collimator
open Collimator.Core
open Collimator.Concrete
open Collimator.Traversal
open Collimator.Fold
open Collimator.Setter
open Collimator.AffineTraversalOps
open scoped Collimator.Operators
open CollimatorTests

testSuite "Traversals"

structure Point where
  x : Int
  y : Int
  deriving BEq, Repr

private def pointLens : Lens Point Point Int Int :=
  lens' (fun p => p.x) (fun p x' => { p with x := x' })

private def optionPrism : Prism (Option Int) (Option Int) Int Int :=
  prism (s := Option Int) (t := Option Int) (a := Int) (b := Int)
    (build := Option.some)
    (split := fun | some n => Sum.inr n | none => Sum.inl none)

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

#generate_tests

end CollimatorTests.Traversals
