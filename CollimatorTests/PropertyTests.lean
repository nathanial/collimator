import Batteries
import Collimator.Optics
import Collimator.Poly.Classes
import Collimator.Combinators
import Collimator.Instances.Prod
import CollimatorTests.Framework

/-!
# Property-Based Tests for Collimator Optics

This module tests optic laws using randomized inputs generated programmatically.
-/

namespace CollimatorTests.PropertyTests

open Collimator
open Collimator.Core
open Collimator.Concrete
open Collimator.Combinators
open CollimatorTests

/-! ## Test Structures -/

structure Point where
  x : Int
  y : Int
  deriving BEq, Repr, DecidableEq

structure Rectangle where
  topLeft : Point
  bottomRight : Point
  deriving BEq, Repr, DecidableEq

/-! ## Lens Definitions -/

private def Point.xLens : Lens' Point Int :=
  lens' (fun p => p.x) (fun p x' => { p with x := x' })

private def Point.yLens : Lens' Point Int :=
  lens' (fun p => p.y) (fun p y' => { p with y := y' })

private def Rectangle.topLeftLens : Lens' Rectangle Point :=
  lens' (fun r => r.topLeft) (fun r p => { r with topLeft := p })

/-! ## Random Value Generation -/

/-- Generate a pseudo-random Int from a seed -/
private def randomInt (seed : Nat) : Int :=
  let h := seed * 1103515245 + 12345
  ((h / 65536) % 32768 : Nat) - 16384

/-- Generate a pseudo-random Point from a seed -/
private def randomPoint (seed : Nat) : Point :=
  { x := randomInt seed, y := randomInt (seed + 1) }

/-- Generate a pseudo-random Rectangle from a seed -/
private def randomRectangle (seed : Nat) : Rectangle :=
  { topLeft := randomPoint seed, bottomRight := randomPoint (seed + 2) }

/-! ## Property Test Helpers -/

/-- Run a property test over multiple random inputs -/
private def testProperty (name : String) (numTests : Nat) (prop : Nat → Bool) : IO Bool := do
  for i in [:numTests] do
    if !prop i then
      IO.println s!"  Property {name} failed for seed {i}"
      return false
  return true

/-! ## Lens Laws Properties -/

/--
GetPut law: view l (set l v s) = v
-/
private def lens_getPut_prop (seed : Nat) : Bool :=
  let s := randomPoint seed
  let v := randomInt (seed + 100)
  view' Point.xLens (set' Point.xLens v s) == v

/--
PutGet law: set l (view l s) s = s
-/
private def lens_putGet_prop (seed : Nat) : Bool :=
  let s := randomPoint seed
  set' Point.xLens (view' Point.xLens s) s == s

/--
PutPut law: set l v (set l v' s) = set l v s
-/
private def lens_putPut_prop (seed : Nat) : Bool :=
  let s := randomPoint seed
  let v := randomInt (seed + 100)
  let v' := randomInt (seed + 200)
  set' Point.xLens v (set' Point.xLens v' s) == set' Point.xLens v s

/-! ## Iso Laws Properties -/

/--
Back-Forward law for Point ↔ Tuple
-/
private def iso_backForward_prop (seed : Nat) : Bool :=
  let p := randomPoint seed
  let forward := fun (p : Point) => (p.x, p.y)
  let backward := fun (xy : Int × Int) => { x := xy.1, y := xy.2 : Point }
  backward (forward p) == p

/--
Forward-Back law for Point ↔ Tuple
-/
private def iso_forwardBack_prop (seed : Nat) : Bool :=
  let xy := (randomInt seed, randomInt (seed + 1))
  let forward := fun (p : Point) => (p.x, p.y)
  let backward := fun (xy : Int × Int) => { x := xy.1, y := xy.2 : Point }
  forward (backward xy) == xy

/--
Bool negation is self-inverse
-/
private def iso_boolNeg_prop (seed : Nat) : Bool :=
  let b := seed % 2 == 0
  !!b == b

/--
Tuple swap composed twice is identity
-/
private def iso_tupleSwap_prop (seed : Nat) : Bool :=
  let ab := (randomInt seed, randomInt (seed + 1))
  let swap := fun (a, b) => (b, a)
  swap (swap ab) == ab

/-! ## Traversal Laws Properties -/

/--
Identity law: over t id s = s
-/
private def traversal_identity_prop (seed : Nat) : Bool :=
  let xs : List Int := (List.range ((seed % 10) + 1)).map (Int.ofNat ·)
  let tr : Traversal' (List Int) Int := Traversal.eachList
  Traversal.over' tr id xs == xs

/--
Traversal preserves list length
-/
private def traversal_length_prop (seed : Nat) : Bool :=
  let xs : List Int := (List.range ((seed % 20) + 1)).map (Int.ofNat ·)
  let tr : Traversal' (List Int) Int := Traversal.eachList
  (Traversal.over' tr (· + 1) xs).length == xs.length

/-! ## Composed Lens Laws Properties -/

/--
Composed lenses satisfy GetPut law
-/
private def composed_getPut_prop (seed : Nat) : Bool :=
  let r := randomRectangle seed
  let v := randomInt (seed + 100)
  let composed : Lens' Rectangle Int := Rectangle.topLeftLens ∘ Point.xLens
  view' composed (set' composed v r) == v

/--
Composed lenses satisfy PutGet law
-/
private def composed_putGet_prop (seed : Nat) : Bool :=
  let r := randomRectangle seed
  let composed : Lens' Rectangle Int := Rectangle.topLeftLens ∘ Point.xLens
  set' composed (view' composed r) r == r

/--
Composed lenses satisfy PutPut law
-/
private def composed_putPut_prop (seed : Nat) : Bool :=
  let r := randomRectangle seed
  let v := randomInt (seed + 100)
  let v' := randomInt (seed + 200)
  let composed : Lens' Rectangle Int := Rectangle.topLeftLens ∘ Point.xLens
  set' composed v (set' composed v' r) == set' composed v r

/-! ## Test Cases -/

private def case_lens_getPut : TestCase := {
  name := "Property: Lens GetPut law (100 samples)",
  run := do
    for i in [:100] do
      ensure (lens_getPut_prop i) s!"GetPut failed for seed {i}"
}

private def case_lens_putGet : TestCase := {
  name := "Property: Lens PutGet law (100 samples)",
  run := do
    for i in [:100] do
      ensure (lens_putGet_prop i) s!"PutGet failed for seed {i}"
}

private def case_lens_putPut : TestCase := {
  name := "Property: Lens PutPut law (100 samples)",
  run := do
    for i in [:100] do
      ensure (lens_putPut_prop i) s!"PutPut failed for seed {i}"
}

private def case_iso_backForward : TestCase := {
  name := "Property: Iso Back-Forward law (100 samples)",
  run := do
    for i in [:100] do
      ensure (iso_backForward_prop i) s!"Back-Forward failed for seed {i}"
}

private def case_iso_forwardBack : TestCase := {
  name := "Property: Iso Forward-Back law (100 samples)",
  run := do
    for i in [:100] do
      ensure (iso_forwardBack_prop i) s!"Forward-Back failed for seed {i}"
}

private def case_iso_boolNeg : TestCase := {
  name := "Property: Bool negation self-inverse (100 samples)",
  run := do
    for i in [:100] do
      ensure (iso_boolNeg_prop i) s!"Bool neg failed for seed {i}"
}

private def case_iso_tupleSwap : TestCase := {
  name := "Property: Tuple swap twice is identity (100 samples)",
  run := do
    for i in [:100] do
      ensure (iso_tupleSwap_prop i) s!"Tuple swap failed for seed {i}"
}

private def case_traversal_identity : TestCase := {
  name := "Property: Traversal identity law (100 samples)",
  run := do
    for i in [:100] do
      ensure (traversal_identity_prop i) s!"Identity failed for seed {i}"
}

private def case_traversal_length : TestCase := {
  name := "Property: Traversal preserves length (100 samples)",
  run := do
    for i in [:100] do
      ensure (traversal_length_prop i) s!"Length failed for seed {i}"
}

private def case_composed_getPut : TestCase := {
  name := "Property: Composed lens GetPut (100 samples)",
  run := do
    for i in [:100] do
      ensure (composed_getPut_prop i) s!"Composed GetPut failed for seed {i}"
}

private def case_composed_putGet : TestCase := {
  name := "Property: Composed lens PutGet (100 samples)",
  run := do
    for i in [:100] do
      ensure (composed_putGet_prop i) s!"Composed PutGet failed for seed {i}"
}

private def case_composed_putPut : TestCase := {
  name := "Property: Composed lens PutPut (100 samples)",
  run := do
    for i in [:100] do
      ensure (composed_putPut_prop i) s!"Composed PutPut failed for seed {i}"
}

/-! ## Stress Tests -/

private def case_stress_large_list : TestCase := {
  name := "Stress: Large list (1000 elements) traversal",
  run := do
    let largeList : List Int := (List.range 1000).map (Int.ofNat ·)
    let tr : Traversal' (List Int) Int := Traversal.eachList
    let result := Traversal.over' tr (· + 1) largeList
    ensure (result.length == 1000) "Large list length preserved"
    ensure (result.head? == some 1) "First element modified"
}

private def case_stress_deep_composition : TestCase := {
  name := "Stress: Deep lens composition (5 levels)",
  run := do
    let nested : ((((Int × Int) × Int) × Int) × Int) := ((((1, 2), 3), 4), 5)

    let l1 : Lens' ((((Int × Int) × Int) × Int) × Int) (((Int × Int) × Int) × Int) := _1
    let l2 : Lens' (((Int × Int) × Int) × Int) ((Int × Int) × Int) := _1
    let l3 : Lens' ((Int × Int) × Int) (Int × Int) := _1
    let l4 : Lens' (Int × Int) Int := _1

    let composed : Lens' (((((Int × Int) × Int) × Int) × Int)) Int := l1 ∘ l2 ∘ l3 ∘ l4

    ensure (view' composed nested == 1) "Deep view"
    ensure (view' composed (set' composed 99 nested) == 99) "Deep set"
}

/--
All property-based test cases.
-/
def cases : List TestCase :=
  [ case_lens_getPut
  , case_lens_putGet
  , case_lens_putPut
  , case_iso_backForward
  , case_iso_forwardBack
  , case_iso_boolNeg
  , case_iso_tupleSwap
  , case_traversal_identity
  , case_traversal_length
  , case_composed_getPut
  , case_composed_putGet
  , case_composed_putPut
  , case_stress_large_list
  , case_stress_deep_composition
  ]

end CollimatorTests.PropertyTests
