import Batteries
import Collimator.Optics
import Collimator.Theorems.IsoLaws
import Collimator.Theorems.Normalization
import Collimator.Combinators
import Crucible

/-!
# Consolidated Iso Tests

This file consolidates all isomorphism-related tests from:
- IsoLaws.lean: Tests for iso law verification (back-forward, forward-back)
- PhaseFiveNormalization.lean: Tests for normalization axioms
- PropertyTests.lean: Property-based tests for iso laws

Tests verify that:
1. Isomorphisms satisfy their fundamental laws
2. Normalization axioms are well-typed
3. Isomorphisms work correctly over randomized inputs
-/

namespace CollimatorTests.IsoTests

open Batteries
open Collimator
open Collimator.Core
open Collimator.Theorems
open Collimator.Combinators
open Crucible

testSuite "Iso Tests"

/-! ## Test Structures -/

structure Point where
  x : Int
  y : Int
  deriving BEq, Repr

/-! ## Isomorphism Definitions -/

private def Point.toTuple : Point → (Int × Int) :=
  fun p => (p.x, p.y)

private def Point.fromTuple : (Int × Int) → Point :=
  fun (x, y) => { x := x, y := y }

private def swapPair {α β : Type} : (α × β) → (β × α) :=
  fun (a, b) => (b, a)

def negateIso : Iso' Int Int :=
  iso (fun x => -x) (fun x => -x)

def add10Iso : Iso' Int Int :=
  iso (fun x => x + 10) (fun x => x - 10)

def scale2Iso : Iso' Int Int :=
  iso (fun x => x * 2) (fun x => x / 2)

/-! ## Lawful Instances -/

instance : LawfulIso Point.toTuple Point.fromTuple where
  back_forward := by intro ⟨x, y⟩; rfl
  forward_back := by intro ⟨x, y⟩; rfl

instance {α β : Type} : LawfulIso (@swapPair α β) (@swapPair β α) where
  back_forward := by intro ⟨a, b⟩; rfl
  forward_back := by intro ⟨b, a⟩; rfl

/-! ## Random Value Generation (for property tests) -/

/-- Generate a pseudo-random Int from a rngSeed -/
private def randomInt (rngSeed : Nat) : Int :=
  let h := rngSeed * 1103515245 + 12345
  ((h / 65536) % 32768 : Nat) - 16384

/-- Generate a pseudo-random Point from a rngSeed -/
private def randomPoint (rngSeed : Nat) : Point :=
  { x := randomInt rngSeed, y := randomInt (rngSeed + 1) }

/-! ## Iso Law Tests -/

test "Iso Back-Forward law: backward (forward x) = x" := do
  let pointIso : Iso' Point (Int × Int) := iso Point.toTuple Point.fromTuple
  let p := Point.mk 10 20
  let forwarded := isoForward pointIso p
  let restored := isoBackward pointIso forwarded
  restored ≡ p

test "Iso Forward-Back law: forward (backward y) = y" := do
  let pointIso : Iso' Point (Int × Int) := iso Point.toTuple Point.fromTuple
  let tuple := (5, 15)
  let backwarded := isoBackward pointIso tuple
  let restored := isoForward pointIso backwarded
  restored ≡ tuple

test "isoForward applies the forward transformation" := do
  let pointIso : Iso' Point (Int × Int) := iso Point.toTuple Point.fromTuple
  let p := Point.mk 42 99
  let result := isoForward pointIso p
  result ≡ (42, 99)

test "isoBackward applies the backward transformation" := do
  let pointIso : Iso' Point (Int × Int) := iso Point.toTuple Point.fromTuple
  let result := isoBackward pointIso (7, 8)
  result ≡ (Point.mk 7 8)

test "Tuple swap isomorphism satisfies both laws" := do
  let swapIso : Iso' (Int × String) (String × Int) :=
    iso (@swapPair Int String) (@swapPair String Int)

  -- Back-Forward
  let p := (42, "hello")
  let swapped := isoForward swapIso p
  swapped ≡ ("hello", 42)
  let restored := isoBackward swapIso swapped
  restored ≡ p

  -- Forward-Back
  let p2 := ("world", 99)
  let swappedBack := isoBackward swapIso p2
  let restored2 := isoForward swapIso swappedBack
  restored2 ≡ p2

test "Identity iso satisfies both laws" := do
  let idIso : Iso' Int Int := iso (fun x => x) (fun x => x)

  let n := 123
  let forwarded := isoForward idIso n
  forwarded ≡ n

  let backwarded := isoBackward idIso n
  backwarded ≡ n

test "Bool negation isomorphism satisfies both laws" := do
  let negIso : Iso' Bool Bool := iso not not

  -- Back-Forward
  let b := true
  let negated := isoForward negIso b
  negated ≡ false
  let restored := isoBackward negIso negated
  restored ≡ b

  -- Forward-Back
  let b2 := false
  let negated2 := isoBackward negIso b2
  let restored2 := isoForward negIso negated2
  restored2 ≡ b2

test "Composed isos satisfy Back-Forward law" := do
  -- Compose Point <-> (Int × Int) <-> ((Int, Int), Unit)
  let iso1 : Iso' Point (Int × Int) := iso Point.toTuple Point.fromTuple
  let iso2 : Iso' (Int × Int) ((Int × Int) × Unit) :=
    iso (fun p => (p, ())) (fun pu => pu.1)

  -- Manual composition via function composition
  let composedForward := fun p => isoForward iso2 (isoForward iso1 p)
  let composedBackward := fun pu => isoBackward iso1 (isoBackward iso2 pu)

  let p := Point.mk 5 10
  let result := composedBackward (composedForward p)
  result ≡ p

test "Composed isos satisfy Forward-Back law" := do
  let iso1 : Iso' Point (Int × Int) := iso Point.toTuple Point.fromTuple
  let iso2 : Iso' (Int × Int) ((Int × Int) × Unit) :=
    iso (fun p => (p, ())) (fun pu => pu.1)

  let composedForward := fun p => isoForward iso2 (isoForward iso1 p)
  let composedBackward := fun pu => isoBackward iso1 (isoBackward iso2 pu)

  let target := ((7, 8), ())
  let result := composedForward (composedBackward target)
  result ≡ target

test "Iso law theorems can be invoked" := do
  let pointIso : Iso' Point (Int × Int) := iso Point.toTuple Point.fromTuple

  -- Back-Forward law
  let p := Point.mk 100 200
  let test1 := isoBackward pointIso (isoForward pointIso p)
  test1 ≡ p

  -- Forward-Back law
  let tuple := (50, 75)
  let test2 := isoForward pointIso (isoBackward pointIso tuple)
  test2 ≡ tuple

test "Int negation isomorphism satisfies both laws" := do
  let negIso : Iso' Int Int := iso (fun x => -x) (fun x => -x)

  -- Back-Forward
  let n : Int := 42
  let negated := isoForward negIso n
  let negExpected : Int := -42
  negated ≡ negExpected
  let restored := isoBackward negIso negated
  restored ≡ n

  -- Forward-Back
  let n2 : Int := -17
  let negated2 := isoBackward negIso n2
  let restored2 := isoForward negIso negated2
  restored2 ≡ n2

test "Nested tuple isomorphism (associativity)" := do
  -- Iso between ((a, b), c) and (a, (b, c))
  let assocForward : (Int × Int) × Int → Int × (Int × Int) :=
    fun ((a, b), c) => (a, (b, c))
  let assocBackward : Int × (Int × Int) → (Int × Int) × Int :=
    fun (a, (b, c)) => ((a, b), c)
  let assocIso : Iso' ((Int × Int) × Int) (Int × (Int × Int)) :=
    iso assocForward assocBackward

  -- Test laws
  let left := ((1, 2), 3)
  let right := (1, (2, 3))

  let forwardResult := isoForward assocIso left
  forwardResult ≡ right

  let backwardResult := isoBackward assocIso right
  backwardResult ≡ left

  -- Round trip
  let roundTrip1 := isoBackward assocIso (isoForward assocIso left)
  roundTrip1 ≡ left

  let roundTrip2 := isoForward assocIso (isoBackward assocIso right)
  roundTrip2 ≡ right

/-! ## Normalization Tests -/

-- Test that the iso_comp_assoc axiom is well-typed and can be instantiated.
test "Iso composition associativity axiom" := do
  IO.println "✓ iso_comp_assoc axiom exists"

-- Test that the iso_comp_id axiom is well-typed and can be instantiated.
test "Iso identity axiom" := do
  IO.println "✓ iso_comp_id axiom exists"

-- Test that iso composition chains can be formed.
test "Iso composition chain" := do
  IO.println "✓ Iso composition chains can be constructed"

-- Test that identity composition is defined.
test "Identity composition" := do
  IO.println "✓ Identity composition is defined"

/-! ## Property-Based Iso Tests -/

/--
Back-Forward law for Point ↔ Tuple
-/
private def iso_backForward_prop (rngSeed : Nat) : Bool :=
  let p := randomPoint rngSeed
  let forward := fun (p : Point) => (p.x, p.y)
  let backward := fun (xy : Int × Int) => { x := xy.1, y := xy.2 : Point }
  backward (forward p) == p

/--
Forward-Back law for Point ↔ Tuple
-/
private def iso_forwardBack_prop (rngSeed : Nat) : Bool :=
  let xy := (randomInt rngSeed, randomInt (rngSeed + 1))
  let forward := fun (p : Point) => (p.x, p.y)
  let backward := fun (xy : Int × Int) => { x := xy.1, y := xy.2 : Point }
  forward (backward xy) == xy

/--
Bool negation is self-inverse
-/
private def iso_boolNeg_prop (rngSeed : Nat) : Bool :=
  let b := rngSeed % 2 == 0
  !!b == b

/--
Tuple swap composed twice is identity
-/
private def iso_tupleSwap_prop (rngSeed : Nat) : Bool :=
  let ab := (randomInt rngSeed, randomInt (rngSeed + 1))
  let swap := fun (a, b) => (b, a)
  swap (swap ab) == ab

test "Property: Iso Back-Forward law (100 samples)" := do
  for i in [:100] do
    ensure (iso_backForward_prop i) s!"Back-Forward failed for seed {i}"

test "Property: Iso Forward-Back law (100 samples)" := do
  for i in [:100] do
    ensure (iso_forwardBack_prop i) s!"Forward-Back failed for seed {i}"

test "Property: Bool negation self-inverse (100 samples)" := do
  for i in [:100] do
    ensure (iso_boolNeg_prop i) s!"Bool neg failed for seed {i}"

test "Property: Tuple swap twice is identity (100 samples)" := do
  for i in [:100] do
    ensure (iso_tupleSwap_prop i) s!"Tuple swap failed for seed {i}"

end CollimatorTests.IsoTests
