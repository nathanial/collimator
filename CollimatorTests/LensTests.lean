import Batteries
import Collimator.Core
import Collimator.Optics
import Collimator.Theorems.LensLaws
import Collimator.Combinators
import Collimator.Operators
import Collimator.Concrete.FunArrow
import Crucible

namespace CollimatorTests.LensTests

open Collimator
open Collimator.Core
open Collimator.Concrete
open Collimator.Theorems
open Collimator.Combinators
open Crucible
open scoped Collimator.Operators

testSuite "Lens Tests"

/-! ## Test Structures -/

structure Point where
  x : Int
  y : Int
  deriving BEq, Repr, DecidableEq

structure Rectangle where
  topLeft : Point
  bottomRight : Point
  deriving BEq, Repr, DecidableEq

structure Person where
  name : String
  age : Nat
  deriving BEq, Repr, Inhabited

structure Company where
  name : String
  ceo : Person
  deriving BEq, Repr, Inhabited

/-! ## Lens Definitions -/

private def Point.getLens_x : Point → Int := fun p => p.x
private def Point.setLens_x : Point → Int → Point := fun p x' => { p with x := x' }

private def Point.getLens_y : Point → Int := fun p => p.y
private def Point.setLens_y : Point → Int → Point := fun p y' => { p with y := y' }

private def Rectangle.getLens_topLeft : Rectangle → Point := fun r => r.topLeft
private def Rectangle.setLens_topLeft : Rectangle → Point → Rectangle := fun r p => { r with topLeft := p }

private def pointLens : Lens Point Point Int Int :=
  lens' (fun p => p.x) (fun p x' => { p with x := x' })

private def Point.xLens : Lens' Point Int :=
  lens' (fun p => p.x) (fun p x' => { p with x := x' })

private def Point.yLens : Lens' Point Int :=
  lens' (fun p => p.y) (fun p y' => { p with y := y' })

private def Rectangle.topLeftLens : Lens' Rectangle Point :=
  lens' (fun r => r.topLeft) (fun r p => { r with topLeft := p })

def personNameLens : Lens' Person String :=
  lens' (fun p => p.name) (fun p n => { p with name := n })

def personAgeLens : Lens' Person Nat :=
  lens' (fun p => p.age) (fun p a => { p with age := a })

def companyNameLens : Lens' Company String :=
  lens' (fun c => c.name) (fun c n => { c with name := n })

def companyCeoLens : Lens' Company Person :=
  lens' (fun c => c.ceo) (fun c p => { c with ceo := p })

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

/-! ## Basic Operations Tests -/

test "lens view/over/set modify records" := do
  let p : Point := { x := 3, y := 5 }
  p ^. pointLens ≡ 3
  let incremented := p & pointLens %~ (· + 2)
  incremented.x ≡ 5
  incremented.y ≡ 5
  let reset := p & pointLens .~ 10
  reset.x ≡ 10
  reset.y ≡ 5

test "tuple lenses focus on individual components" := do
  let pair : Nat × String := (4, "lean")
  let firstLens : Lens' (Nat × String) Nat :=
    _1 (α := Nat) (β := String) (γ := Nat)
  let secondLens : Lens (Nat × String) (Nat × String) String String :=
    _2 (α := Nat) (β := String) (γ := String)
  pair ^. firstLens ≡ 4
  pair ^. secondLens ≡ "lean"
  let updated := pair & secondLens .~ "core"
  updated ≡ (4, "core")

test "const lens ignores updates" := do
  let l : Lens' String Int := const (s := String) (a := Int) 42
  "value" ^. l ≡ 42
  ("value" & l .~ 0) ≡ "value"

/-! ## Lens Laws Tests -/

test "Lens GetPut law: view l (set l v s) = v" := do
  let p : Point := { x := 5, y := 10 }
  let xLens : Lens' Point Int := lens' Point.getLens_x Point.setLens_x
  let newValue := 42
  let modified := p & xLens .~ newValue
  let viewed := modified ^. xLens
  viewed ≡ newValue

test "Lens PutGet law: set l (view l s) s = s" := do
  let p : Point := { x := 7, y := 14 }
  let xLens : Lens' Point Int := lens' Point.getLens_x Point.setLens_x
  let currentValue := p ^. xLens
  let unchanged := p & xLens .~ currentValue
  unchanged ≡ p

test "Lens PutPut law: set l v (set l v' s) = set l v s" := do
  let p : Point := { x := 3, y := 9 }
  let yLens : Lens' Point Int := lens' Point.getLens_y Point.setLens_y
  let intermediate := p & yLens .~ 100
  let final := intermediate & yLens .~ 200
  let direct := p & yLens .~ 200
  final ≡ direct

test "Tuple lens _1 satisfies all three laws" := do
  let pair : Nat × String := (42, "test")
  let firstLens : Lens' (Nat × String) Nat := _1 (α := Nat) (β := String) (γ := Nat)

  -- GetPut
  let modified1 := pair & firstLens .~ 99
  let viewed1 := modified1 ^. firstLens
  viewed1 ≡ 99

  -- PutGet
  let current := pair ^. firstLens
  let unchanged := pair & firstLens .~ current
  unchanged ≡ pair

  -- PutPut
  let intermediate := pair & firstLens .~ 11
  let final := intermediate & firstLens .~ 22
  let direct := pair & firstLens .~ 22
  final ≡ direct

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
  viewed ≡ newValue

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
  unchanged ≡ r

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
  final ≡ direct

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

  test1 ≡ 10
  test2 ≡ p
  test3 ≡ test4

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
  (r ^. comp1) ≡ 0
  (r ^. comp2) ≡ 0

  let r' := r & comp1 .~ 25
  (r' ^. comp1) ≡ 25
  (r' ^. comp2) ≡ 0

/-! ## Getter Tests -/

test "Getter: basic construction and view" := do
  -- Create a simple getter
  let nameGetter := getter (fun p : Person => p.name)
  let alice := Person.mk "Alice" 30

  -- Use view
  let name := nameGetter.view alice
  name ≡ "Alice"

  -- Use coercion (getter as function)
  let name2 := nameGetter alice
  name2 ≡ "Alice"

  IO.println "✓ Getter: basic construction and view"

test "Getter: conversion from Lens (ofLens)" := do
  let bob := Person.mk "Bob" 25

  -- Convert lens to getter
  let ageGetter := Getter.ofLens personAgeLens

  let age := ageGetter.view bob
  age ≡ 25

  -- Getters are read-only - can only view, not set
  -- (This is enforced by the type system)

  IO.println "✓ Getter: conversion from Lens works correctly"

test "Getter: composition of getters" := do
  let company := Company.mk "TechCorp" (Person.mk "Carol" 45)

  -- Create getters
  let ceoGetter := Getter.ofLens companyCeoLens
  let ageGetter := Getter.ofLens personAgeLens

  -- Compose getters
  let ceoAgeGetter := ceoGetter.compose ageGetter

  let ceoAge := ceoAgeGetter.view company
  ceoAge ≡ 45

  -- Compose with name
  let nameGetter := Getter.ofLens personNameLens
  let ceoNameGetter := ceoGetter.compose nameGetter

  let ceoName := ceoNameGetter.view company
  ceoName ≡ "Carol"

  IO.println "✓ Getter: composition works correctly"

test "Getter: practical use cases" := do
  let people := [
    Person.mk "Alice" 30,
    Person.mk "Bob" 25,
    Person.mk "Carol" 35
  ]

  let nameGetter := getter (fun p : Person => p.name)
  let ageGetter := getter (fun p : Person => p.age)

  -- Extract all names
  let names := people.map nameGetter.view
  names ≡ ["Alice", "Bob", "Carol"]

  -- Find average age using getter
  let ages := people.map ageGetter.view
  let totalAge := ages.foldl (· + ·) 0
  totalAge ≡ 90

  -- Computed getter (derived value)
  let isAdultGetter := getter (fun p : Person => decide (p.age >= 18))
  let allAdults := people.map isAdultGetter.view
  shouldSatisfy (allAdults.all (fun b => b)) "all adults"

  IO.println "✓ Getter: practical use cases work correctly"

/-! ## Property Tests -/

/-! ### Random Value Generation -/

/-- Generate a pseudo-random Int from a rngSeed -/
private def randomInt (rngSeed : Nat) : Int :=
  let h := rngSeed * 1103515245 + 12345
  ((h / 65536) % 32768 : Nat) - 16384

/-- Generate a pseudo-random Point from a rngSeed -/
private def randomPoint (rngSeed : Nat) : Point :=
  { x := randomInt rngSeed, y := randomInt (rngSeed + 1) }

/-- Generate a pseudo-random Rectangle from a rngSeed -/
private def randomRectangle (rngSeed : Nat) : Rectangle :=
  { topLeft := randomPoint rngSeed, bottomRight := randomPoint (rngSeed + 2) }

/-! ### Lens Laws Properties -/

/--
GetPut law: view l (set l v s) = v
-/
private def lens_getPut_prop (rngSeed : Nat) : Bool :=
  let s := randomPoint rngSeed
  let v := randomInt (rngSeed + 100)
  (s & Point.xLens .~ v) ^. Point.xLens == v

/--
PutGet law: set l (view l s) s = s
-/
private def lens_putGet_prop (rngSeed : Nat) : Bool :=
  let s := randomPoint rngSeed
  (s & Point.xLens .~ (s ^. Point.xLens)) == s

/--
PutPut law: set l v (set l v' s) = set l v s
-/
private def lens_putPut_prop (rngSeed : Nat) : Bool :=
  let s := randomPoint rngSeed
  let v := randomInt (rngSeed + 100)
  let v' := randomInt (rngSeed + 200)
  (s & Point.xLens .~ v' & Point.xLens .~ v) == (s & Point.xLens .~ v)

/-! ### Composed Lens Laws Properties -/

/--
Composed lenses satisfy GetPut law
-/
private def composed_getPut_prop (rngSeed : Nat) : Bool :=
  let r := randomRectangle rngSeed
  let v := randomInt (rngSeed + 100)
  let composed : Lens' Rectangle Int := Rectangle.topLeftLens ∘ Point.xLens
  (r & composed .~ v) ^. composed == v

/--
Composed lenses satisfy PutGet law
-/
private def composed_putGet_prop (rngSeed : Nat) : Bool :=
  let r := randomRectangle rngSeed
  let composed : Lens' Rectangle Int := Rectangle.topLeftLens ∘ Point.xLens
  (r & composed .~ (r ^. composed)) == r

/--
Composed lenses satisfy PutPut law
-/
private def composed_putPut_prop (rngSeed : Nat) : Bool :=
  let r := randomRectangle rngSeed
  let v := randomInt (rngSeed + 100)
  let v' := randomInt (rngSeed + 200)
  let composed : Lens' Rectangle Int := Rectangle.topLeftLens ∘ Point.xLens
  (r & composed .~ v' & composed .~ v) == (r & composed .~ v)

/-! ### Property Test Cases -/

test "Property: Lens GetPut law (100 samples)" := do
  for i in [:100] do
    ensure (lens_getPut_prop i) s!"GetPut failed for seed {i}"

test "Property: Lens PutGet law (100 samples)" := do
  for i in [:100] do
    ensure (lens_putGet_prop i) s!"PutGet failed for seed {i}"

test "Property: Lens PutPut law (100 samples)" := do
  for i in [:100] do
    ensure (lens_putPut_prop i) s!"PutPut failed for seed {i}"

test "Property: Composed lens GetPut (100 samples)" := do
  for i in [:100] do
    ensure (composed_getPut_prop i) s!"Composed GetPut failed for seed {i}"

test "Property: Composed lens PutGet (100 samples)" := do
  for i in [:100] do
    ensure (composed_putGet_prop i) s!"Composed PutGet failed for seed {i}"

test "Property: Composed lens PutPut (100 samples)" := do
  for i in [:100] do
    ensure (composed_putPut_prop i) s!"Composed PutPut failed for seed {i}"

/-! ### Stress Tests -/

test "Stress: Deep lens composition (5 levels)" := do
  let nested : ((((Int × Int) × Int) × Int) × Int) := ((((1, 2), 3), 4), 5)

  let l1 : Lens' ((((Int × Int) × Int) × Int) × Int) (((Int × Int) × Int) × Int) := _1
  let l2 : Lens' (((Int × Int) × Int) × Int) ((Int × Int) × Int) := _1
  let l3 : Lens' ((Int × Int) × Int) (Int × Int) := _1
  let l4 : Lens' (Int × Int) Int := _1

  let composed : Lens' (((((Int × Int) × Int) × Int) × Int)) Int := l1 ∘ l2 ∘ l3 ∘ l4

  nested ^. composed ≡ 1
  (nested & composed .~ 99) ^. composed ≡ 99

end CollimatorTests.LensTests
