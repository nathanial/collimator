import Batteries
import Collimator.Theorems.Subtyping
import Collimator.Optics
import CollimatorTests.Framework

/-!
# Phase 5 Subtyping Tests

Tests for optic subtyping preservation theorems.

These tests verify that the subtyping axioms are properly stated and accessible.
The axioms establish that lawfulness is preserved when using more specific optics
in contexts expecting more general optics.
-/

namespace CollimatorTests.PhaseFiveSubtyping

open Collimator
open Collimator.Theorems
open CollimatorTests

/-! ## Test Structures -/

structure Point where
  x : Int
  y : Int
  deriving BEq, Repr

/-! ## Test Cases -/

/--
Test that the subtyping module compiles and is accessible.
-/
private def case_subtyping_module_accessible : TestCase := {
  name := "Subtyping module: Compiles successfully",
  run := do
    -- The module exists and compiles
    -- All axioms are properly declared
    pure ()
}

/--
Test that iso_to_lens_preserves_laws can be invoked and produces a lawful lens.
-/
private def case_iso_to_lens_theorem : TestCase := {
  name := "iso_to_lens_preserves_laws: Iso becomes lawful lens",
  run := do
    -- Define forward and backward functions
    let forward : Point → (Int × Int) := fun p => (p.x, p.y)
    let back : (Int × Int) → Point := fun (x, y) => { x := x, y := y }

    -- Prove they form a lawful iso
    let lawful_iso : LawfulIso forward back := {
      back_forward := by intro ⟨x, y⟩; rfl
      forward_back := by intro ⟨x, y⟩; rfl
    }

    -- The theorem guarantees existence, so we just verify it typechecks
    -- and produces the expected result type
    let _result : ∃ (get : Point → (Int × Int)) (set : Point → (Int × Int) → Point),
                     LawfulLens get set :=
      @iso_to_lens_preserves_laws Point (Int × Int) forward back lawful_iso

    -- Test the constructed lens operations directly
    let get := forward
    let set := fun (_ : Point) (a : Int × Int) => back a

    -- Test the lens operations
    let p := Point.mk 10 20

    -- Test get
    let tuple := get p
    ensureEq "Get extracts tuple" (10, 20) tuple

    -- Test set
    let p' := set p (5, 15)
    ensureEq "Set creates new point" (Point.mk 5 15) p'

    -- Verify GetPut law: get (set s v) = v
    let v := (7, 8)
    let s := Point.mk 100 200
    let test1 := get (set s v)
    ensureEq "GetPut law holds" v test1

    -- Verify PutGet law: set s (get s) = s
    let test2 := set s (get s)
    ensureEq "PutGet law holds" s test2

    -- Verify PutPut law: set (set s v) v' = set s v'
    let v' := (9, 10)
    let test3_double := set (set s v) v'
    let test3_single := set s v'
    ensureEq "PutPut law holds" test3_single test3_double
}

/--
Test iso_to_lens with Bool negation isomorphism.
-/
private def case_iso_to_lens_bool_negation : TestCase := {
  name := "iso_to_lens_preserves_laws: Bool negation iso as lens",
  run := do
    let forward : Bool → Bool := not
    let back : Bool → Bool := not

    let lawful_iso : LawfulIso forward back := {
      back_forward := by intro x; cases x <;> rfl
      forward_back := by intro x; cases x <;> rfl
    }

    let _result : ∃ (get : Bool → Bool) (set : Bool → Bool → Bool), LawfulLens get set :=
      @iso_to_lens_preserves_laws Bool Bool forward back lawful_iso

    -- Test the constructed lens operations directly
    let get := forward
    let set := fun (_ : Bool) (b : Bool) => back b

    -- Test the lens
    ensureEq "Get negates" false (get true)
    ensureEq "Get negates 2" true (get false)

    -- The lens set ignores the current state (that's the key property)
    -- set ignores first arg and applies 'not' to second arg
    ensureEq "Set true to false" true (set true false)  -- not false = true
    ensureEq "Set false to false" true (set false false)  -- not false = true
    ensureEq "Set true to true" false (set true true)  -- not true = false
    ensureEq "Set false to true" false (set false true)  -- not true = false
}

/--
Test that iso_to_prism_preserves_laws can be invoked and produces a lawful prism.
-/
private def case_iso_to_prism_theorem : TestCase := {
  name := "iso_to_prism_preserves_laws: Iso becomes lawful prism",
  run := do
    -- Define forward and backward functions
    let forward : Point → (Int × Int) := fun p => (p.x, p.y)
    let back : (Int × Int) → Point := fun (x, y) => { x := x, y := y }

    -- Prove they form a lawful iso
    let lawful_iso : LawfulIso forward back := {
      back_forward := by intro ⟨x, y⟩; rfl
      forward_back := by intro ⟨x, y⟩; rfl
    }

    -- The theorem guarantees existence
    let _result : ∃ (build : (Int × Int) → Point) (split : Point → Sum Point (Int × Int)),
                     LawfulPrism build split :=
      @iso_to_prism_preserves_laws Point (Int × Int) forward back lawful_iso

    -- Test the constructed prism operations directly
    let build := back
    let split : Point → Sum Point (Int × Int) := fun x => Sum.inr (forward x)

    -- Test build
    let p := build (10, 20)
    ensureEq "Build creates point" (Point.mk 10 20) p

    -- Test split - iso always succeeds
    let s := Point.mk 5 15
    match split s with
    | Sum.inl _ => throw (IO.userError "Split should never fail for iso")
    | Sum.inr tuple => ensureEq "Split extracts tuple" (5, 15) tuple

    -- Verify Preview-Review law: split (build b) = Sum.inr b
    let b := (7, 8)
    match split (build b) with
    | Sum.inl _ => throw (IO.userError "Preview-Review should succeed")
    | Sum.inr result => ensureEq "Preview-Review law holds" b result

    -- Verify Review-Preview law: split s = Sum.inr a → build a = s
    let s2 := Point.mk 100 200
    match split s2 with
    | Sum.inl _ => throw (IO.userError "Split should always succeed for iso")
    | Sum.inr a => do
      let rebuilt := build a
      ensureEq "Review-Preview law holds" s2 rebuilt
}

/--
Test iso_to_prism with Bool negation isomorphism.
-/
private def case_iso_to_prism_bool_negation : TestCase := {
  name := "iso_to_prism_preserves_laws: Bool negation iso as prism",
  run := do
    let forward : Bool → Bool := not
    let back : Bool → Bool := not

    let lawful_iso : LawfulIso forward back := {
      back_forward := by intro x; cases x <;> rfl
      forward_back := by intro x; cases x <;> rfl
    }

    let _result : ∃ (build : Bool → Bool) (split : Bool → Sum Bool Bool), LawfulPrism build split :=
      @iso_to_prism_preserves_laws Bool Bool forward back lawful_iso

    -- Test the constructed prism operations directly
    let build := back
    let split : Bool → Sum Bool Bool := fun x => Sum.inr (forward x)

    -- Test that split always succeeds (iso never fails)
    match split true with
    | Sum.inl _ => throw (IO.userError "Split should succeed")
    | Sum.inr b => ensureEq "Split true gives false" false b

    match split false with
    | Sum.inl _ => throw (IO.userError "Split should succeed")
    | Sum.inr b => ensureEq "Split false gives true" true b

    -- Test build
    ensureEq "Build false gives true" true (build false)
    ensureEq "Build true gives false" false (build true)

    -- Verify round-trip
    match split (build true) with
    | Sum.inl _ => throw (IO.userError "Round-trip should succeed")
    | Sum.inr result => ensureEq "Round-trip preserves value" true result
}

/--
Test that lens_to_affine_preserves_laws can be invoked and produces a lawful affine traversal.
-/
private def case_lens_to_affine_theorem : TestCase := {
  name := "lens_to_affine_preserves_laws: Lens becomes lawful affine traversal",
  run := do
    -- Define get and set for Point ↔ (Int × Int) lens
    let get : Point → (Int × Int) := fun p => (p.x, p.y)
    let set_lens : Point → (Int × Int) → Point :=
      fun _ (x, y) => { x := x, y := y }

    -- Prove it's a lawful lens
    let lawful_lens : LawfulLens get set_lens := {
      getput := by intro s v; rfl
      putget := by intro ⟨x, y⟩; rfl
      putput := by intro s v v'; rfl
    }

    -- The theorem guarantees existence of lawful affine operations
    let _result : ∃ (preview : Point → Option (Int × Int))
                     (set_aff : Point → (Int × Int) → Point),
                    LawfulAffineTraversal preview set_aff :=
      @lens_to_affine_preserves_laws Point (Int × Int) get set_lens lawful_lens

    -- Test the affine operations directly
    let preview : Point → Option (Int × Int) := fun s => some (get s)
    let set_aff : Point → (Int × Int) → Point := set_lens

    let p := Point.mk 10 20

    -- Test preview - should always succeed for lens-derived affine
    match preview p with
    | none => throw (IO.userError "Preview should succeed")
    | some tuple => ensureEq "Preview extracts tuple" (10, 20) tuple

    -- Test set
    let p' := set_aff p (5, 15)
    ensureEq "Set creates new point" (Point.mk 5 15) p'

    -- Verify SetPreview law: preview (set s v) = some v
    let v := (7, 8)
    match preview (set_aff p v) with
    | none => throw (IO.userError "SetPreview should succeed")
    | some result => ensureEq "SetPreview law holds" v result

    -- Verify PreviewSet law: preview s = some a → set s a = s
    match preview p with
    | none => throw (IO.userError "Preview should succeed")
    | some a => do
      let restored := set_aff p a
      ensureEq "PreviewSet law holds" p restored

    -- Verify SetSet law: set (set s v) v' = set s v'
    let v' := (9, 10)
    let double := set_aff (set_aff p v) v'
    let single := set_aff p v'
    ensureEq "SetSet law holds" single double
}

/--
Test lens_to_affine with Int negation lens (identity structure).
-/
private def case_lens_to_affine_simple : TestCase := {
  name := "lens_to_affine_preserves_laws: Simple Int lens as affine",
  run := do
    -- Identity lens on Int (get = id, set = const id)
    let get : Int → Int := fun x => x
    let set_lens : Int → Int → Int := fun _ v => v

    let lawful_lens : LawfulLens get set_lens := {
      getput := by intro s v; rfl
      putget := by intro s; rfl
      putput := by intro s v v'; rfl
    }

    let _result : ∃ (preview : Int → Option Int) (set_aff : Int → Int → Int),
                    LawfulAffineTraversal preview set_aff :=
      @lens_to_affine_preserves_laws Int Int get set_lens lawful_lens

    -- Test the operations
    let preview : Int → Option Int := fun s => some (get s)
    let set_aff : Int → Int → Int := set_lens

    -- Preview always succeeds
    match preview 42 with
    | none => throw (IO.userError "Preview should succeed")
    | some n => ensureEq "Preview gets value" 42 n

    -- Set works
    ensureEq "Set replaces value" 99 (set_aff 42 99)

    -- All three laws hold (tested above in the main test)
}

/--
Test lens_to_affine with field lens.
-/
private def case_lens_to_affine_field_lens : TestCase := {
  name := "lens_to_affine_preserves_laws: Field lens (x coordinate) as affine",
  run := do
    -- Lens focusing on x coordinate
    let get : Point → Int := fun p => p.x
    let set_lens : Point → Int → Point := fun p v => { p with x := v }

    let lawful_lens : LawfulLens get set_lens := {
      getput := by intro s v; rfl
      putget := by intro ⟨x, y⟩; rfl
      putput := by intro s v v'; rfl
    }

    let _result : ∃ (preview : Point → Option Int) (set_aff : Point → Int → Point),
                    LawfulAffineTraversal preview set_aff :=
      @lens_to_affine_preserves_laws Point Int get set_lens lawful_lens

    -- Test operations
    let preview : Point → Option Int := fun s => some (get s)
    let set_aff : Point → Int → Point := set_lens

    let p := Point.mk 10 20

    -- Preview gets x coordinate
    match preview p with
    | none => throw (IO.userError "Preview should succeed")
    | some x => ensureEq "Preview gets x" 10 x

    -- Set updates x
    let p' := set_aff p 99
    ensureEq "Set updates x" (Point.mk 99 20) p'

    -- Verify laws
    -- SetPreview: preview (set p v) = some v
    match preview (set_aff p 42) with
    | none => throw (IO.userError "SetPreview should succeed")
    | some x => ensureEq "SetPreview law" 42 x

    -- PreviewSet: set p (get p) = p
    match preview p with
    | none => throw (IO.userError "Preview should succeed")
    | some a => ensureEq "PreviewSet law" p (set_aff p a)
}

/-! ## Test Suite -/

def cases : List TestCase := [
  case_subtyping_module_accessible,
  case_iso_to_lens_theorem,
  case_iso_to_lens_bool_negation,
  case_iso_to_prism_theorem,
  case_iso_to_prism_bool_negation,
  case_lens_to_affine_theorem,
  case_lens_to_affine_simple,
  case_lens_to_affine_field_lens
]

end CollimatorTests.PhaseFiveSubtyping
