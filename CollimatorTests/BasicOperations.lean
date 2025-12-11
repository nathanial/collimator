import Collimator.Core
import Batteries
import Collimator.Optics
import Collimator.Concrete.FunArrow
import CollimatorTests.Framework

namespace CollimatorTests.BasicOperations

open Collimator
open Collimator.Core
open Collimator.Concrete
open CollimatorTests

structure Point where
  x : Int
  y : Int
  deriving BEq, Repr

private def pointLens : Lens Point Point Int Int :=
  lens' (fun p => p.x) (fun p x' => { p with x := x' })

private def case_isoDimap : TestCase := {
  name := "iso dimap composes forward and backward maps",
  run := do
    let shiftIso : Iso Int Int Int Int :=
      iso (s := Int) (t := Int) (a := Int) (b := Int)
        (forward := fun n => n + 1) (back := fun n => n - 1)
    let double := FunArrow.mk (fun n : Int => n * 2)
    -- With type-alias optics, the iso IS the polymorphic function
    let mapped := shiftIso (P := fun α β => FunArrow α β) double
    ensureEq "iso applies dimap" 7 (mapped 3)
}

private def case_lensViewOverSet : TestCase := {
  name := "lens view/over/set modify records",
  run := do
    let p : Point := { x := 3, y := 5 }
    ensureEq "view extracts field" 3 (view' pointLens p)
    let incremented := over' pointLens (fun n => n + 2) p
    ensureEq "over updates field" 5 incremented.x
    ensureEq "over preserves other fields" 5 incremented.y
    let reset := set' pointLens 10 p
    ensureEq "set replaces field" 10 reset.x
    ensureEq "set preserves other fields" 5 reset.y
}

private def case_tupleLenses : TestCase := {
  name := "tuple lenses focus on individual components",
  run := do
    let pair : Nat × String := (4, "lean")
    let firstLens : Lens' (Nat × String) Nat :=
      _1 (α := Nat) (β := String) (γ := Nat)
    let secondLens : Lens (Nat × String) (Nat × String) String String :=
      _2 (α := Nat) (β := String) (γ := String)
    ensureEq "_1 views first" 4 (view' firstLens pair)
    ensureEq "_2 views second" "lean" (view' secondLens pair)
    let updated := set' secondLens "core" pair
    ensureEq "set _2 replaces second" (4, "core") updated
}

private def case_constLens : TestCase := {
  name := "const lens ignores updates",
  run := do
    let l : Lens' String Int := const (s := String) (a := Int) 42
    ensureEq "view const" 42 (view' l "value")
    ensureEq "set const returns original" "value" ((set' l 0) "value")
}

private def optionPrism : Prism (Sum Unit Nat) (Sum Unit Nat) Nat Nat :=
  prism (s := Sum Unit Nat) (t := Sum Unit Nat) (a := Nat) (b := Nat)
    (build := Sum.inr)
    (split :=
      fun
      | Sum.inl u => Sum.inl (Sum.inl u)
      | Sum.inr n => Sum.inr n)

private def case_prismPreviewReview : TestCase := {
  name := "prism preview/review works for sums",
  run := do
    ensureEq "preview extracts right" (some 7) (preview' optionPrism (Sum.inr 7))
    ensureEq "preview rejects left" (none : Option Nat) (preview' optionPrism (Sum.inl ()))
    ensureEq "review injects" (Sum.inr 9) (review' optionPrism 9)
}

/--
All Phase 2 optic test cases.
-/
def cases : List TestCase :=
  [ case_isoDimap
  , case_lensViewOverSet
  , case_tupleLenses
  , case_constLens
  , case_prismPreviewReview
  ]

end CollimatorTests.BasicOperations
