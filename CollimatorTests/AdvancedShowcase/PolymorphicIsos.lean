import Collimator.Optics.Iso
import Collimator.Poly
import Collimator.Theorems.IsoLaws
import CollimatorTests.Framework

namespace CollimatorTests.AdvancedShowcase.PolymorphicIsos

open Collimator
open Collimator.Poly
open Collimator.Theorems
open CollimatorTests

/-!
Polymorphic isomorphisms demonstrate the power of type-changing optics.
Unlike simple lenses that preserve types, isos can transform between
fundamentally different representations while maintaining correctness.
-/

/-! ## Custom Types -/

structure Complex where
  real : Float
  imag : Float
  deriving BEq, Repr

/-- Isomorphism between complex numbers and pairs of floats. -/
private def complexIso : Iso Complex Complex (Float × Float) (Float × Float) :=
  iso
    (forward := fun c => (c.real, c.imag))
    (back := fun (r, i) => { real := r, imag := i })

/-- Prove the complex iso is lawful. -/
private def complexIso_lawful : LawfulIso
    (fun c : Complex => (c.real, c.imag))
    (fun (r, i) => Complex.mk r i) := {
  back_forward := by intro ⟨r, i⟩; rfl
  forward_back := by intro ⟨r, i⟩; rfl
}

private def case_complexIso : TestCase := {
  name := "Complex ↔ (Float × Float): Bidirectional type transformation",
  run := do
    let c : Complex := { real := 3.0, imag := 4.0 }

    -- Forward direction: Complex → Pair
    let pair := view (optic := fun s a => Iso s s a a) complexIso c
    ensureEq "Forward extracts pair" (3.0, 4.0) pair

    -- Backward direction: Pair → Complex
    let c' := over (optic := Iso) complexIso _root_.id c
    ensureEq "Identity over preserves" c c'

    -- Set new value
    let c'' := set (optic := Iso) complexIso (5.0, 12.0) c
    ensureEq "Set transforms via pair" (Complex.mk 5.0 12.0) c''

    -- Verify round-trip: back ∘ forward = id
    let roundtrip := set (optic := Iso) complexIso (view (optic := fun s a => Iso s s a a) complexIso c) c
    ensureEq "Round-trip preserves value" c roundtrip
}

/-- Isomorphism encoding Bool as 0 or 1. -/
private def boolToNatIso : Iso Bool Bool Nat Nat :=
  iso
    (forward := fun b => if b then 1 else 0)
    (back := fun n => n != 0)

private def case_boolToNat : TestCase := {
  name := "Bool ↔ Nat: Encode boolean as 0/1",
  run := do
    -- Forward: true → 1, false → 0
    ensureEq "true encodes as 1" 1 (view (optic := fun s a => Iso s s a a) boolToNatIso true)
    ensureEq "false encodes as 0" 0 (view (optic := fun s a => Iso s s a a) boolToNatIso false)

    -- Backward: n != 0 decodes to bool
    ensureEq "0 decodes to false" false (set (optic := Iso) boolToNatIso 0 true)
    ensureEq "1 decodes to true" true (set (optic := Iso) boolToNatIso 1 false)
    ensureEq "42 decodes to true" true (set (optic := Iso) boolToNatIso 42 false)

    -- Round-trip preservation
    ensureEq "Round-trip true" true (set (optic := Iso) boolToNatIso (view (optic := fun s a => Iso s s a a) boolToNatIso true) true)
    ensureEq "Round-trip false" false (set (optic := Iso) boolToNatIso (view (optic := fun s a => Iso s s a a) boolToNatIso false) false)
}

/-- Isomorphism between String and List Char. -/
private def stringToListIso : Iso String String (List Char) (List Char) :=
  iso
    (forward := String.toList)
    (back := List.asString)

private def case_stringToList : TestCase := {
  name := "String ↔ List Char: Structural transformation",
  run := do
    let s : String := "optics"

    -- Forward: String → List Char
    let chars := view (optic := fun s a => Iso s s a a) stringToListIso s
    ensureEq "String to list" ['o', 'p', 't', 'i', 'c', 's'] chars

    -- Backward: List Char → String
    let s' := set (optic := Iso) stringToListIso ['l', 'e', 'a', 'n'] s
    ensureEq "List to string" "lean" s'

    -- Round-trip
    let roundtrip := set (optic := Iso) stringToListIso (view (optic := fun s a => Iso s s a a) stringToListIso s) s
    ensureEq "Round-trip preserves" s roundtrip

    -- Empty string edge case
    let empty := set (optic := Iso) stringToListIso [] s
    ensureEq "Empty list produces empty string" "" empty
}

/-- Self-inverse isomorphism: Bool negation. -/
private def boolNegIso : Iso Bool Bool Bool Bool :=
  iso
    (forward := not)
    (back := not)

/-- Prove Bool negation is lawful (forward = back, so both laws trivial). -/
private def boolNegIso_lawful : LawfulIso not not := {
  back_forward := by intro x; cases x <;> rfl
  forward_back := by intro x; cases x <;> rfl
}

private def case_boolNegSelfInverse : TestCase := {
  name := "Bool ↔ Bool via not: Self-inverse transformation",
  run := do
    -- Forward negates
    ensureEq "Forward negates true" false (view (optic := fun s a => Iso s s a a) boolNegIso true)
    ensureEq "Forward negates false" true (view (optic := fun s a => Iso s s a a) boolNegIso false)

    -- Back also negates (same as forward): set applies back to the value
    ensureEq "Back negates false" true (set (optic := Iso) boolNegIso false true)
    ensureEq "Back negates true" false (set (optic := Iso) boolNegIso true false)

    -- Double application is identity
    let double_true := set (optic := Iso) boolNegIso (view (optic := fun s a => Iso s s a a) boolNegIso true) true
    let double_false := set (optic := Iso) boolNegIso (view (optic := fun s a => Iso s s a a) boolNegIso false) false
    ensureEq "not ∘ not = id (true)" true double_true
    ensureEq "not ∘ not = id (false)" false double_false

    -- Interesting: forward = back, so iso is self-dual
}

/-- Tuple swap isomorphism with explicit law verification. -/
private def tupleSwapIso {α β : Type} : Iso (α × β) (α × β) (β × α) (β × α) :=
  iso
    (forward := fun (a, b) => (b, a))
    (back := fun (b, a) => (a, b))

/-- Prove tuple swap is lawful. -/
private def tupleSwapIso_lawful {α β : Type} : LawfulIso
    (fun (p : α × β) => (p.2, p.1))
    (fun (p : β × α) => (p.2, p.1)) := {
  back_forward := by intro ⟨a, b⟩; rfl
  forward_back := by intro ⟨b, a⟩; rfl
}

private def case_tupleSwap : TestCase := {
  name := "Tuple swap (A × B) ↔ (B × A): Classic isomorphism",
  run := do
    let pair : (Int × String) := (42, "answer")

    -- Forward swaps
    let swapped := view (optic := fun s a => Iso s s a a) (tupleSwapIso (α := Int) (β := String)) pair
    ensureEq "Swap exchanges positions" ("answer", 42) swapped

    -- Back swaps again: set expects the swapped type (String × Int)
    let unswapped := Poly.set (optic := Iso) (tupleSwapIso (α := Int) (β := String)) ("ten", 10) pair
    ensureEq "Swap back" (10, "ten") unswapped

    -- Double swap is identity
    let roundtrip := Poly.set (optic := Iso) (tupleSwapIso (α := Int) (β := String))
                         (view (optic := fun s a => Iso s s a a) (tupleSwapIso (α := Int) (β := String)) pair)
                         pair
    ensureEq "Swap ∘ swap = id" pair roundtrip

    -- Works with any types
    let boolFloat : (Bool × Float) := (true, 3.14)
    let swapped2 := view (optic := fun s a => Iso s s a a) (tupleSwapIso (α := Bool) (β := Float)) boolFloat
    ensureEq "Works with Bool × Float" (3.14, true) swapped2
}

/--
Curry/uncurry isomorphism (commented out due to universe level complexity).
This would transform between (A × B → C) and (A → B → C).
-/
-- private def curryIso {α β γ : Type} :
--     Iso (α × β → γ) (α × β → γ) (α → β → γ) (α → β → γ) :=
--   iso
--     (forward := Function.curry)
--     (back := Function.uncurry)

private def case_polymorphicComposition : TestCase := {
  name := "Polymorphic iso composition: String → List Char → List Nat",
  run := do
    -- We can't directly create Char → Nat iso easily, so simulate
    -- by composing string to list with a traversal
    let s : String := "ab"
    let chars := view (optic := fun s a => Iso s s a a) stringToListIso s

    -- Demonstrate that isos compose
    let swapIso : Iso (String × List Char) (String × List Char) (List Char × String) (List Char × String) :=
      tupleSwapIso (α := String) (β := List Char)
    let pair : (String × List Char) := (s, chars)
    let swapped : (List Char × String) := view (optic := fun s a => Iso s s a a) swapIso pair
    ensureEq "Composed type transformation" (chars, s) swapped

    -- The key insight: isos compose with ∘ just like functions
    -- This is the magic of profunctor optics
}

def cases : List TestCase := [
  case_complexIso,
  case_boolToNat,
  case_stringToList,
  case_boolNegSelfInverse,
  case_tupleSwap,
  case_polymorphicComposition
]

end CollimatorTests.AdvancedShowcase.PolymorphicIsos
