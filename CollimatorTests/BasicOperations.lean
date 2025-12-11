import Collimator.Core
import Batteries
import Collimator.Optics
import Collimator.Operators
import Collimator.Concrete.FunArrow
import CollimatorTests.Framework

namespace CollimatorTests.BasicOperations

open Collimator
open Collimator.Core
open Collimator.Concrete
open scoped Collimator.Operators
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
    ensureEq "view extracts field" 3 (p ^. pointLens)
    let incremented := p & pointLens %~ (· + 2)
    ensureEq "over updates field" 5 incremented.x
    ensureEq "over preserves other fields" 5 incremented.y
    let reset := p & pointLens .~ 10
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
    ensureEq "_1 views first" 4 (pair ^. firstLens)
    ensureEq "_2 views second" "lean" (pair ^. secondLens)
    let updated := pair & secondLens .~ "core"
    ensureEq "set _2 replaces second" (4, "core") updated
}

private def case_constLens : TestCase := {
  name := "const lens ignores updates",
  run := do
    let l : Lens' String Int := const (s := String) (a := Int) 42
    ensureEq "view const" 42 ("value" ^. l)
    ensureEq "set const returns original" "value" ("value" & l .~ 0)
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
    ensureEq "preview extracts right" (some 7) ((Sum.inr 7) ^? optionPrism)
    ensureEq "preview rejects left" (none : Option Nat) ((Sum.inl ()) ^? optionPrism)
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
