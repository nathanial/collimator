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

private def case_traversalOverList : TestCase := {
  name := "traversal over updates each list element",
  run := do
    let tr : Traversal' (List Int) Int := Traversal.eachList
    let updated := [1, 2, 3] & tr %~ (· + 1)
    ensureEq "list increment" [2, 3, 4] updated
}

private def case_traverseOptionEffect : TestCase := {
  name := "traversal traverse short-circuits via option applicative",
  run := do
    let tr : Traversal' (List Int) Int := Traversal.eachList
    let step : Int → Option Int := fun n => if n ≥ 0 then some (n + 1) else none
    let success := Traversal.traverse' tr step [0, 2]
    let failure := Traversal.traverse' tr step [0, -1, 3]
    ensureEq "success case" (some [1, 3]) success
    ensureEq "failure case" (none : Option (List Int)) failure
}

private def case_foldToList : TestCase := {
  name := "fold toList collects focuses in order",
  run := do
    let fld : Fold' (Option Int) Int :=
      Fold.ofAffine (s := Option Int) (t := Option Int) (a := Int) (b := Int)
        (AffineTraversalOps.ofPrism optionPrism)
    ensureEq "some" [7] (Fold.toList fld (some 7))
    ensureEq "none" ([] : List Int) (Fold.toList fld none)
}

private def case_foldAggregates : TestCase := {
  name := "fold foldMap aggregates via monoid",
  run := do
    let fld : Fold' Point Int := Fold.ofLens pointLens
    let points := [{ x := 2, y := 1 }, { x := -1, y := 5 }, { x := 4, y := 9 }]
    let lifted := points.map (Fold.toList fld)
    ensureEq "values fold" ([[2], [-1], [4]] : List (List Int)) lifted
}

private def case_foldLength : TestCase := {
  name := "fold length counts focuses",
  run := do
    let fld : Fold' Point Int := Fold.ofLens pointLens
    ensureEq "single focus" 1 ((Fold.toList fld { x := 5, y := 0 }).length)
}

private def case_setterSet : TestCase := {
  name := "setter set updates value",
  run := do
    let st : Lens' Point Int := pointLens
    let updated := { x := 1, y := 2 } & st .~ 42
    ensureEq "setter set" { x := 42, y := 2 } updated
}

private def case_affinePreviewAndSet : TestCase := {
  name := "affine traversal preview and set behaves correctly",
  run := do
    let affine : AffineTraversal' (Option Int) Int :=
      AffineTraversalOps.ofPrism optionPrism
    ensureEq "preview some" (some 5) ((some 5) ^? affine)
    ensureEq "preview none" (none : Option Int) (none ^? affine)
    let reset := (some 1) & affine .~ 99
    ensureEq "set value" (some 99) reset
}

/--
All traversals optic test cases.
-/
def cases : List TestCase :=
  [ case_traversalOverList
  , case_traverseOptionEffect
  , case_foldToList
  , case_foldAggregates
  , case_foldLength
  , case_setterSet
  , case_affinePreviewAndSet
  ]

end CollimatorTests.Traversals
