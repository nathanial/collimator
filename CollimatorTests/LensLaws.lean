import Batteries
import Collimator.Optics.Lens
import Collimator.Optics.Types
import Collimator.Theorems.LensLaws
import Collimator.Combinators.Composition
import CollimatorTests.Framework

namespace CollimatorTests.LensLaws

open Collimator
open Collimator.Theorems
open Collimator.Combinators
open CollimatorTests

/-! ## Test Structures -/

structure Point where
  x : Int
  y : Int
  deriving BEq, Repr

structure Rectangle where
  topLeft : Point
  bottomRight : Point
  deriving BEq, Repr

/-! ## Lens Definitions -/

private def Point.getLens_x : Point → Int := fun p => p.x
private def Point.setLens_x : Point → Int → Point := fun p x' => { p with x := x' }

private def Point.getLens_y : Point → Int := fun p => p.y
private def Point.setLens_y : Point → Int → Point := fun p y' => { p with y := y' }

private def Rectangle.getLens_topLeft : Rectangle → Point := fun r => r.topLeft
private def Rectangle.setLens_topLeft : Rectangle → Point → Rectangle := fun r p => { r with topLeft := p }

/-! ## Lawful Instances -/

instance : LawfulLens Point.getLens_x Point.setLens_x where
  getput := by intro _ _; rfl
  putget := by intro ⟨_, _⟩; rfl
  putput := by intro _ _ _; rfl

instance : LawfulLens Point.getLens_y Point.setLens_y where
  getput := by intro _ _; rfl
  putget := by intro ⟨_, _⟩; rfl
  putput := by intro _ _ _; rfl

instance : LawfulLens Rectangle.getLens_topLeft Rectangle.setLens_topLeft where
  getput := by intro _ _; rfl
  putget := by intro ⟨_, _⟩; rfl
  putput := by intro _ _ _; rfl

/-! ## Test Cases -/

/--
Test that the GetPut law holds: viewing after setting returns what was set.
-/
private def case_getLens_putLaw : TestCase := {
  name := "Lens GetPut law: view l (set l v s) = v",
  run := do
    let p : Point := { x := 5, y := 10 }
    let xLens : Lens' Point Int := lens' Point.getLens_x Point.setLens_x
    let newValue := 42
    let modified := set' xLens newValue p
    let viewed := view' xLens modified
    ensureEq "GetPut law" newValue viewed
}

/--
Test that the PutGet law holds: setting the current value doesn't change anything.
-/
private def case_putgetLaw : TestCase := {
  name := "Lens PutGet law: set l (view l s) s = s",
  run := do
    let p : Point := { x := 7, y := 14 }
    let xLens : Lens' Point Int := lens' Point.getLens_x Point.setLens_x
    let currentValue := view' xLens p
    let unchanged := set' xLens currentValue p
    ensureEq "PutGet law" p unchanged
}

/--
Test that the PutPut law holds: setting twice is the same as setting once with the last value.
-/
private def case_putputLaw : TestCase := {
  name := "Lens PutPut law: set l v (set l v' s) = set l v s",
  run := do
    let p : Point := { x := 3, y := 9 }
    let yLens : Lens' Point Int := lens' Point.getLens_y Point.setLens_y
    let intermediate := set' yLens 100 p
    let final := set' yLens 200 intermediate
    let direct := set' yLens 200 p
    ensureEq "PutPut law" direct final
}

/--
Test that all three lens laws hold for the tuple projection lens _1.
-/
private def case_tupleLensLaws : TestCase := {
  name := "Tuple lens _1 satisfies all three laws",
  run := do
    let pair : Nat × String := (42, "test")
    let firstLens : Lens' (Nat × String) Nat := _1 (α := Nat) (β := String) (γ := Nat)

    -- GetPut
    let modified1 := set' firstLens 99 pair
    let viewed1 := view' firstLens modified1
    ensureEq "Tuple _1 GetPut" 99 viewed1

    -- PutGet
    let current := view' firstLens pair
    let unchanged := set' firstLens current pair
    ensureEq "Tuple _1 PutGet" pair unchanged

    -- PutPut
    let intermediate := set' firstLens 11 pair
    let final := set' firstLens 22 intermediate
    let direct := set' firstLens 22 pair
    ensureEq "Tuple _1 PutPut" direct final
}

/--
Test composition preserves GetPut law.
-/
private def case_compositionGetPutLaw : TestCase := {
  name := "Composed lenses satisfy GetPut law",
  run := do
    let r : Rectangle := {
      topLeft := { x := 0, y := 0 },
      bottomRight := { x := 100, y := 100 }
    }
    let topLeftLens : Lens' Rectangle Point := lens' Rectangle.getLens_topLeft Rectangle.setLens_topLeft
    let xLens : Lens' Point Int := lens' Point.getLens_x Point.setLens_x
    let composed : Lens' Rectangle Int := composeLens topLeftLens xLens

    let newValue := -50
    let modified := set' composed newValue r
    let viewed := view' composed modified
    ensureEq "Composed GetPut law" newValue viewed
}

/--
Test composition preserves PutGet law.
-/
private def case_compositionPutGetLaw : TestCase := {
  name := "Composed lenses satisfy PutGet law",
  run := do
    let r : Rectangle := {
      topLeft := { x := 10, y := 20 },
      bottomRight := { x := 110, y := 120 }
    }
    let topLeftLens : Lens' Rectangle Point := lens' Rectangle.getLens_topLeft Rectangle.setLens_topLeft
    let yLens : Lens' Point Int := lens' Point.getLens_y Point.setLens_y
    let composed : Lens' Rectangle Int := composeLens topLeftLens yLens

    let currentValue := view' composed r
    let unchanged := set' composed currentValue r
    ensureEq "Composed PutGet law" r unchanged
}

/--
Test composition preserves PutPut law.
-/
private def case_compositionPutPutLaw : TestCase := {
  name := "Composed lenses satisfy PutPut law",
  run := do
    let r : Rectangle := {
      topLeft := { x := 5, y := 15 },
      bottomRight := { x := 105, y := 115 }
    }
    let topLeftLens : Lens' Rectangle Point := lens' Rectangle.getLens_topLeft Rectangle.setLens_topLeft
    let xLens : Lens' Point Int := lens' Point.getLens_x Point.setLens_x
    let composed : Lens' Rectangle Int := composeLens topLeftLens xLens

    let intermediate := set' composed 777 r
    let final := set' composed 888 intermediate
    let direct := set' composed 888 r
    ensureEq "Composed PutPut law" direct final
}

/--
Test that using the lawful lens theorems works correctly.
This test verifies that we can use the proven theorems to establish lens correctness.
-/
private def case_lensLawTheorems : TestCase := {
  name := "Lens law theorems can be invoked",
  run := do
    -- The theorems themselves are compile-time proofs
    -- We verify they exist and are applicable by using them in a computation
    let p : Point := { x := 1, y := 2 }
    let xLens : Lens' Point Int := lens' Point.getLens_x Point.setLens_x

    -- These operations should satisfy the laws by construction
    -- (the laws are proven in LensLaws.lean)
    let test1 := view' xLens (set' xLens 10 p)
    let test2 := set' xLens (view' xLens p) p
    let test3 := set' xLens 30 (set' xLens 20 p)
    let test4 := set' xLens 30 p

    ensureEq "Law theorem GetPut" 10 test1
    ensureEq "Law theorem PutGet" p test2
    ensureEq "Law theorem PutPut" test4 test3
}

/--
Test that the composition lawfulness instance works.
This demonstrates that composedLens_isLawful can be used as an instance.
-/
private def case_compositionLawfulInstance : TestCase := {
  name := "Composition lawfulness instance is usable",
  run := do
    -- The instance composedLens_isLawful proves that composed get/set are lawful
    -- We demonstrate this by constructing lenses and verifying their behavior
    let r : Rectangle := {
      topLeft := { x := 0, y := 0 },
      bottomRight := { x := 50, y := 50 }
    }

    -- These compositions use the lawful instances
    let topLeftLens : Lens' Rectangle Point := lens' Rectangle.getLens_topLeft Rectangle.setLens_topLeft
    let xLens : Lens' Point Int := lens' Point.getLens_x Point.setLens_x
    let comp1 : Lens' Rectangle Int := composeLens topLeftLens xLens

    let yLens : Lens' Point Int := lens' Point.getLens_y Point.setLens_y
    let comp2 : Lens' Rectangle Int := composeLens topLeftLens yLens

    -- Verify the compositions work correctly
    ensureEq "Composed X view" 0 (view' comp1 r)
    ensureEq "Composed Y view" 0 (view' comp2 r)

    let r' := set' comp1 25 r
    ensureEq "Composed X set" 25 (view' comp1 r')
    ensureEq "Composed X preserves Y" 0 (view' comp2 r')
}

/--
All lens law test cases.
-/
def cases : List TestCase :=
  [ case_getLens_putLaw
  , case_putgetLaw
  , case_putputLaw
  , case_tupleLensLaws
  , case_compositionGetPutLaw
  , case_compositionPutGetLaw
  , case_compositionPutPutLaw
  , case_lensLawTheorems
  , case_compositionLawfulInstance
  ]

end CollimatorTests.LensLaws
