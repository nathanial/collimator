import Batteries
import Collimator.Optics
import Collimator.Theorems.LensLaws
import Collimator.Combinators
import Collimator.Operators
import CollimatorTests.Framework

namespace CollimatorTests.LensLaws

open Collimator
open Collimator.Theorems
open Collimator.Combinators
open CollimatorTests
open scoped Collimator.Operators

testSuite "Lens Laws"

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

test "Lens GetPut law: view l (set l v s) = v" := do
  let p : Point := { x := 5, y := 10 }
  let xLens : Lens' Point Int := lens' Point.getLens_x Point.setLens_x
  let newValue := 42
  let modified := p & xLens .~ newValue
  let viewed := modified ^. xLens
  ensureEq "GetPut law" newValue viewed

test "Lens PutGet law: set l (view l s) s = s" := do
  let p : Point := { x := 7, y := 14 }
  let xLens : Lens' Point Int := lens' Point.getLens_x Point.setLens_x
  let currentValue := p ^. xLens
  let unchanged := p & xLens .~ currentValue
  ensureEq "PutGet law" p unchanged

test "Lens PutPut law: set l v (set l v' s) = set l v s" := do
  let p : Point := { x := 3, y := 9 }
  let yLens : Lens' Point Int := lens' Point.getLens_y Point.setLens_y
  let intermediate := p & yLens .~ 100
  let final := intermediate & yLens .~ 200
  let direct := p & yLens .~ 200
  ensureEq "PutPut law" direct final

test "Tuple lens _1 satisfies all three laws" := do
  let pair : Nat × String := (42, "test")
  let firstLens : Lens' (Nat × String) Nat := _1 (α := Nat) (β := String) (γ := Nat)

  -- GetPut
  let modified1 := pair & firstLens .~ 99
  let viewed1 := modified1 ^. firstLens
  ensureEq "Tuple _1 GetPut" 99 viewed1

  -- PutGet
  let current := pair ^. firstLens
  let unchanged := pair & firstLens .~ current
  ensureEq "Tuple _1 PutGet" pair unchanged

  -- PutPut
  let intermediate := pair & firstLens .~ 11
  let final := intermediate & firstLens .~ 22
  let direct := pair & firstLens .~ 22
  ensureEq "Tuple _1 PutPut" direct final

test "Composed lenses satisfy GetPut law" := do
  let r : Rectangle := {
    topLeft := { x := 0, y := 0 },
    bottomRight := { x := 100, y := 100 }
  }
  let topLeftLens : Lens' Rectangle Point := lens' Rectangle.getLens_topLeft Rectangle.setLens_topLeft
  let xLens : Lens' Point Int := lens' Point.getLens_x Point.setLens_x
  let composed : Lens' Rectangle Int := topLeftLens ∘ xLens

  let newValue := -50
  let modified := r & composed .~ newValue
  let viewed := modified ^. composed
  ensureEq "Composed GetPut law" newValue viewed

test "Composed lenses satisfy PutGet law" := do
  let r : Rectangle := {
    topLeft := { x := 10, y := 20 },
    bottomRight := { x := 110, y := 120 }
  }
  let topLeftLens : Lens' Rectangle Point := lens' Rectangle.getLens_topLeft Rectangle.setLens_topLeft
  let yLens : Lens' Point Int := lens' Point.getLens_y Point.setLens_y
  let composed : Lens' Rectangle Int := topLeftLens ∘ yLens

  let currentValue := r ^. composed
  let unchanged := r & composed .~ currentValue
  ensureEq "Composed PutGet law" r unchanged

test "Composed lenses satisfy PutPut law" := do
  let r : Rectangle := {
    topLeft := { x := 5, y := 15 },
    bottomRight := { x := 105, y := 115 }
  }
  let topLeftLens : Lens' Rectangle Point := lens' Rectangle.getLens_topLeft Rectangle.setLens_topLeft
  let xLens : Lens' Point Int := lens' Point.getLens_x Point.setLens_x
  let composed : Lens' Rectangle Int := topLeftLens ∘ xLens

  let intermediate := r & composed .~ 777
  let final := intermediate & composed .~ 888
  let direct := r & composed .~ 888
  ensureEq "Composed PutPut law" direct final

test "Lens law theorems can be invoked" := do
  -- The theorems themselves are compile-time proofs
  -- We verify they exist and are applicable by using them in a computation
  let p : Point := { x := 1, y := 2 }
  let xLens : Lens' Point Int := lens' Point.getLens_x Point.setLens_x

  -- These operations should satisfy the laws by construction
  -- (the laws are proven in LensLaws.lean)
  let test1 := (p & xLens .~ 10) ^. xLens
  let test2 := p & xLens .~ (p ^. xLens)
  let test3 := p & xLens .~ 20 & xLens .~ 30
  let test4 := p & xLens .~ 30

  ensureEq "Law theorem GetPut" 10 test1
  ensureEq "Law theorem PutGet" p test2
  ensureEq "Law theorem PutPut" test4 test3

test "Composition lawfulness instance is usable" := do
  -- The instance composedLens_isLawful proves that composed get/set are lawful
  -- We demonstrate this by constructing lenses and verifying their behavior
  let r : Rectangle := {
    topLeft := { x := 0, y := 0 },
    bottomRight := { x := 50, y := 50 }
  }

  -- These compositions use the lawful instances
  let topLeftLens : Lens' Rectangle Point := lens' Rectangle.getLens_topLeft Rectangle.setLens_topLeft
  let xLens : Lens' Point Int := lens' Point.getLens_x Point.setLens_x
  let comp1 : Lens' Rectangle Int := topLeftLens ∘ xLens

  let yLens : Lens' Point Int := lens' Point.getLens_y Point.setLens_y
  let comp2 : Lens' Rectangle Int := topLeftLens ∘ yLens

  -- Verify the compositions work correctly
  ensureEq "Composed X view" 0 (r ^. comp1)
  ensureEq "Composed Y view" 0 (r ^. comp2)

  let r' := r & comp1 .~ 25
  ensureEq "Composed X set" 25 (r' ^. comp1)
  ensureEq "Composed X preserves Y" 0 (r' ^. comp2)

#generate_tests

end CollimatorTests.LensLaws
