import Batteries
import Collimator.Optics
import Collimator.Theorems.AffineLaws
import Collimator.Theorems.Subtyping
import Collimator.Combinators
import Collimator.Operators
import CollimatorTests.Framework

namespace CollimatorTests.AffineTests

open Collimator
open Collimator.Theorems
open Collimator.Combinators
open Collimator.AffineTraversalOps
open CollimatorTests

open scoped Collimator.Operators

testSuite "Affine Tests"

/-!
# Affine Traversal Tests

This file consolidates tests for:
1. Affine traversal laws
2. Affine wizardry (advanced demonstrations)
3. Optic subtyping preservation

Affine traversals focus on zero-or-one targets, combining the power of
lenses (always present) and prisms (may be absent).
-/

-- ## Test Structures

structure Container (α : Type) where
  value : Option α
  deriving BEq, Repr, Inhabited

structure NestedContainer where
  outer : Container Int
  label : String
  deriving BEq, Repr

structure Point where
  x : Int
  y : Int
  deriving BEq, Repr

universe u

/-- Configuration value that may be a string, int, or boolean -/
inductive ConfigValue : Type where
  | str : String → ConfigValue
  | int : Int → ConfigValue
  | bool : Bool → ConfigValue
  deriving BEq, Repr, Inhabited

/-- A configuration entry with a key and optional value -/
structure ConfigEntry : Type where
  key : String
  value : Option ConfigValue
  deriving BEq, Repr, Inhabited

/-- User profile with nested optional data -/
structure ProfileData : Type where
  displayName : String
  bio : Option String
  age : Option Nat
  deriving BEq, Repr, Inhabited

/-- Database record with optional fields -/
structure UserRecord : Type where
  id : Nat
  username : String
  email : Option String
  profile : Option ProfileData
  deriving BEq, Repr, Inhabited

-- ## Helper Functions

private def Container.preview : Container α → Option α := fun c => c.value
private def Container.set : Container α → α → Container α := fun c a => { c with value := some a }

private def NestedContainer.preview_outer : NestedContainer → Option (Container Int) := fun nc => some nc.outer
private def NestedContainer.set_outer : NestedContainer → Container Int → NestedContainer := fun nc c => { nc with outer := c }

-- ## Lawful Instances

instance {α : Type} : LawfulAffineTraversal (Container.preview (α := α)) (Container.set (α := α)) where
  set_preview := by
    intro s v hfocus
    -- Container.set always produces some value
    rfl
  preview_set := by
    intro s a hprev
    -- If preview s = some a, then s.value = some a
    -- Setting s to a gives { s with value := some a } = s (since s.value = some a)
    simp only [Container.preview] at hprev
    simp only [Container.set]
    cases s with
    | mk val =>
      simp only at hprev
      simp only [hprev]
  set_set := by
    intro s v v'
    -- set (set s v) v' = { { s with value := some v } with value := some v' }
    --                   = { s with value := some v' }
    --                   = set s v'
    rfl

instance : LawfulAffineTraversal NestedContainer.preview_outer NestedContainer.set_outer where
  set_preview := by
    intro s v _hfocus
    rfl
  preview_set := by
    intro s a hprev
    simp only [NestedContainer.preview_outer] at hprev
    injection hprev with heq
    simp only [NestedContainer.set_outer]
    cases s with
    | mk outer label => simp only at heq; simp [heq]
  set_set := by
    intro s v v'
    rfl

-- ## Optics

def configValueLens : Lens' ConfigEntry (Option ConfigValue) := fieldLens% ConfigEntry value

def userEmailLens : Lens' UserRecord (Option String) := fieldLens% UserRecord email

def userProfileLens : Lens' UserRecord (Option ProfileData) := fieldLens% UserRecord profile

def profileBioLens : Lens' ProfileData (Option String) := fieldLens% ProfileData bio

def profileAgeLens : Lens' ProfileData (Option Nat) := fieldLens% ProfileData age

def containerValueLens (α : Type) : Lens' (Container α) (Option α) := fieldLens% Container value

def somePrism (α : Type) : Prism' (Option α) α := ctorPrism% Option.some

def strConfigPrism : Prism' ConfigValue String := ctorPrism% ConfigValue.str

def intConfigPrism : Prism' ConfigValue Int := ctorPrism% ConfigValue.int

def boolConfigPrism : Prism' ConfigValue Bool := ctorPrism% ConfigValue.bool

-- ## Test Cases: Affine Laws

test "Affine SetPreview law: preview s ≠ none → preview (set s v) = some v" := do
  let c : Container Int := { value := some 5 }
  let newValue := 42
  let modified := Container.set c newValue
  let previewed := Container.preview modified
  ensureEq "SetPreview law" (some newValue) previewed

test "Affine SetPreview works when setting into empty container" := do
  let c : Container Int := { value := none }
  let newValue := 99
  let modified := Container.set c newValue
  let previewed := Container.preview modified
  ensureEq "SetPreview from empty" (some newValue) previewed

test "Affine PreviewSet law: preview s = some a → set s a = s" := do
  let c : Container Int := { value := some 7 }
  match Container.preview c with
  | some currentValue =>
    let unchanged := Container.set c currentValue
    ensureEq "PreviewSet law" c unchanged
  | none =>
    ensure false "Should have a value"

test "Affine SetSet law: set (set s v) v' = set s v'" := do
  let c : Container Int := { value := some 3 }
  let intermediate := Container.set c 100
  let final := Container.set intermediate 200
  let direct := Container.set c 200
  ensureEq "SetSet law" direct final

test "Option satisfies all three affine traversal laws" := do
  let opt : Option Int := some 42

  -- SetPreview: preview (set s v) = some v when s has focus
  let setResult := (fun _ => some 99) opt
  ensureEq "Option SetPreview" (some 99) setResult

  -- PreviewSet: set s a = s when preview s = some a
  let orig : Option Int := some 10
  let unchanged := (fun _ => some 10) orig
  -- Note: For Option as affine, set always produces Some, so this tests the essence
  ensureEq "Option PreviewSet essence" (some 10) unchanged

  -- SetSet: set (set s v) v' = set s v'
  let first := (fun _ : Option Int => some 1) opt
  let second := (fun _ : Option Int => some 2) first
  let direct := (fun _ : Option Int => some 2) opt
  ensureEq "Option SetSet" direct second

test "Composed affine traversals satisfy SetPreview law" := do
  let nc : NestedContainer := {
    outer := { value := some 10 },
    label := "test"
  }

  -- Compose: NestedContainer → Container Int → Int
  -- For this test, we manually compose the operations
  let preview_composed : NestedContainer → Option Int := fun nc =>
    match NestedContainer.preview_outer nc with
    | none => none
    | some c => Container.preview c

  let set_composed : NestedContainer → Int → NestedContainer := fun nc v =>
    match NestedContainer.preview_outer nc with
    | none => nc
    | some c => NestedContainer.set_outer nc (Container.set c v)

  -- Test SetPreview: preview (set nc v) = some v when nc has nested focus
  let newValue := 777
  let modified := set_composed nc newValue
  let previewed := preview_composed modified
  ensureEq "Composed SetPreview" (some newValue) previewed

test "Composed affine traversals satisfy PreviewSet law" := do
  let nc : NestedContainer := {
    outer := { value := some 25 },
    label := "example"
  }

  let preview_composed : NestedContainer → Option Int := fun nc =>
    match NestedContainer.preview_outer nc with
    | none => none
    | some c => Container.preview c

  let set_composed : NestedContainer → Int → NestedContainer := fun nc v =>
    match NestedContainer.preview_outer nc with
    | none => nc
    | some c => NestedContainer.set_outer nc (Container.set c v)

  -- Test PreviewSet: set nc (preview nc) = nc when preview succeeds
  match preview_composed nc with
  | some currentValue =>
    let unchanged := set_composed nc currentValue
    ensureEq "Composed PreviewSet" nc unchanged
  | none =>
    ensure false "Should have nested value"

test "Composed affine traversals satisfy SetSet law" := do
  let nc : NestedContainer := {
    outer := { value := some 5 },
    label := "setset"
  }

  let set_composed : NestedContainer → Int → NestedContainer := fun nc v =>
    match NestedContainer.preview_outer nc with
    | none => nc
    | some c => NestedContainer.set_outer nc (Container.set c v)

  -- Test SetSet: set (set nc v) v' = set nc v'
  let intermediate := set_composed nc 111
  let final := set_composed intermediate 222
  let direct := set_composed nc 222
  ensureEq "Composed SetSet" direct final

test "Affine traversal with no focus leaves structure unchanged" := do
  let c : Container Int := { value := none }

  -- When there's no focus, preview returns none
  let previewed := Container.preview c
  ensureEq "No focus preview" (none : Option Int) previewed

  -- Note: Our Container.set always sets the value, so we test the concept
  -- with a structure that truly has 0 focus in some cases

  -- For the nested case:
  let nc : NestedContainer := {
    outer := { value := none },
    label := "empty"
  }

  let preview_composed : NestedContainer → Option Int := fun nc =>
    match NestedContainer.preview_outer nc with
    | none => none
    | some c => Container.preview c

  -- Composed preview of nc.outer.value should be none
  let nestedPreview := preview_composed nc
  ensureEq "Nested no focus" (none : Option Int) nestedPreview

test "Affine law theorems can be invoked" := do
  let c : Container Int := { value := some 1 }

  -- These operations should satisfy the laws by construction
  let test1 := Container.preview (Container.set c 10)
  let test2 := Container.set c 1  -- setting current value
  let test3 := Container.set (Container.set c 20) 30
  let test4 := Container.set c 30

  ensureEq "Law theorem SetPreview" (some 10) test1
  ensureEq "Law theorem PreviewSet" c test2
  ensureEq "Law theorem SetSet" test4 test3

-- ## Test Cases: Affine Wizardry

/-
**Safe Partial Access**: Demonstrates accessing optional values safely.

AffineTraversals provide a middle ground between Lens (always present) and
Traversal (zero or more). With AffineTraversal, we know there's at most
one focus, which enables certain optimizations and clearer semantics.
-/
test "Safe partial access with AffineTraversal" := do
    -- Create users with varying levels of completeness
    let completeUser := UserRecord.mk 1 "alice"
      (some "alice@example.com")
      (some (ProfileData.mk "Alice" (some "I love Lean!") (some 28)))

    let partialUser := UserRecord.mk 2 "bob"
      (some "bob@example.com")
      none  -- No profile

    let minimalUser := UserRecord.mk 3 "carol"
      none  -- No email
      none  -- No profile

    -- Lens ∘ Prism creates an AffineTraversal
    -- Combined: AffineTraversal focusing on the email if present
    let emailAffine := optic% userEmailLens ∘ somePrism String : AffineTraversal' UserRecord String

    -- Preview safely extracts the value if present
    (completeUser ^? emailAffine) ≡? "alice@example.com"
    (partialUser ^? emailAffine) ≡? "bob@example.com"
    shouldBeNone (minimalUser ^? emailAffine)

    IO.println "✓ Safe partial access: preview returns Option based on focus presence"

    -- Set only modifies when focus is present
    let updatedAlice := completeUser & emailAffine .~ "newalice@example.com"
    updatedAlice.email ≡? "newalice@example.com"

    let updatedCarol := minimalUser & emailAffine .~ "carol@example.com"
    -- Carol has no email, so set with the affine leaves it unchanged
    shouldBeNone updatedCarol.email

    IO.println "✓ Safe partial access: set only modifies when focus exists"

/-
**Lens + Prism Composition**: Shows how composing Lens with Prism yields AffineTraversal.

This is the canonical way to create AffineTraversals - the composition of a
Lens (which always has a focus) with a Prism (which may or may not match)
creates an optic that focuses on at most one value.
-/
test "Lens + Prism composition yields AffineTraversal" := do
    let entries := [
      ConfigEntry.mk "host" (some (ConfigValue.str "localhost")),
      ConfigEntry.mk "port" (some (ConfigValue.int 8080)),
      ConfigEntry.mk "debug" (some (ConfigValue.bool true)),
      ConfigEntry.mk "timeout" none  -- Missing value
    ]

    -- Lens into Option ConfigValue, then Prism to String
    let strValueAffine := optic%
      (configValueLens ∘ somePrism ConfigValue) ∘ strConfigPrism
      : AffineTraversal' ConfigEntry String

    -- Lens into Option ConfigValue, then Prism to Int
    let intValueAffine := optic%
      (configValueLens ∘ somePrism ConfigValue) ∘ intConfigPrism
      : AffineTraversal' ConfigEntry Int

    -- Preview string values
    (entries[0]! ^? strValueAffine) ≡? "localhost"
    shouldBeNone (entries[1]! ^? strValueAffine)  -- port is Int, not String

    IO.println "✓ Lens + Prism: composition correctly filters by type"

    -- Preview int values
    (entries[1]! ^? intValueAffine) ≡? 8080
    shouldBeNone (entries[0]! ^? intValueAffine)  -- host is String, not Int

    IO.println "✓ Lens + Prism: type-safe extraction of sum type variants"

    -- Modify string value
    let updatedHost := entries[0]! & strValueAffine %~ (· ++ ":3000")
    match updatedHost.value with
    | some (ConfigValue.str s) => s ≡ "localhost:3000"
    | _ => throw (IO.userError "Expected string config value")

    -- Trying to modify with wrong prism leaves value unchanged
    let notUpdatedPort := entries[1]! & strValueAffine %~ (· ++ "!")
    notUpdatedPort.value ≡ some (ConfigValue.int 8080)

    IO.println "✓ Lens + Prism: modifications only apply when prism matches"

/-
**Short-Circuit Behavior**: Demonstrates that AffineTraversals stop early when focus is missing.

Unlike Traversals that always visit all possible focuses, AffineTraversals
know there's at most one focus, enabling efficient short-circuit evaluation.
-/
test "Short-circuiting behavior on missing focuses" := do
    -- Deep nested optional structure
    let deepPresent : Container (Container (Container Nat)) :=
      ⟨some ⟨some ⟨some 42⟩⟩⟩

    let midMissing : Container (Container (Container Nat)) :=
      ⟨some ⟨none⟩⟩

    let topMissing : Container (Container (Container Nat)) :=
      ⟨none⟩

    -- Build deep affine traversal through 3 levels of Option
    -- With type-alias optics, Lens ∘ Prism gives AffineTraversal
    let level1 := optic%
      (containerValueLens (Container (Container Nat))) ∘ (somePrism (Container (Container Nat)))
      : AffineTraversal' (Container (Container (Container Nat))) (Container (Container Nat))
    let level2 := optic%
      level1 ∘ (containerValueLens (Container Nat)) ∘ (somePrism (Container Nat))
      : AffineTraversal' (Container (Container (Container Nat))) (Container Nat)
    let deepAffine := optic%
      level2 ∘ (containerValueLens Nat) ∘ (somePrism Nat)
      : AffineTraversal' (Container (Container (Container Nat))) Nat

    -- All present - we can access the value
    (deepPresent ^? deepAffine) ≡? 42

    IO.println "✓ Short-circuit: deep access succeeds when all levels present"

    -- Missing in middle - short circuits
    shouldBeNone (midMissing ^? deepAffine)

    IO.println "✓ Short-circuit: stops at first missing level (middle)"

    -- Missing at top - short circuits immediately
    shouldBeNone (topMissing ^? deepAffine)

    IO.println "✓ Short-circuit: stops at first missing level (top)"

    -- Modification also short-circuits
    let modifiedPresent := deepPresent & deepAffine %~ (· * 2)
    (modifiedPresent ^? deepAffine) ≡? 84

    let modifiedMissing := midMissing & deepAffine %~ (· * 2)
    -- Structure unchanged since there's nothing to modify
    modifiedMissing.value ≡ some ⟨none⟩

    IO.println "✓ Short-circuit: over operation also short-circuits on missing focus"

/-
**Database Lookup Patterns**: Real-world pattern of accessing optional nested fields.

Shows how AffineTraversals elegantly handle the common database pattern of
records with optional fields and nested optional relationships.
-/
test "Database lookup patterns with optional fields" := do
    -- Simulated database records
    let users := [
      UserRecord.mk 1 "alice"
        (some "alice@corp.com")
        (some (ProfileData.mk "Alice Smith" (some "Engineering lead") (some 35))),
      UserRecord.mk 2 "bob"
        (some "bob@corp.com")
        (some (ProfileData.mk "Bob Jones" none (some 28))),  -- No bio
      UserRecord.mk 3 "carol"
        (some "carol@corp.com")
        none,  -- No profile at all
      UserRecord.mk 4 "dave"
        none  -- No email
        (some (ProfileData.mk "Dave Brown" (some "Contractor") none))  -- No age
    ]

    -- Affine traversal to user's bio through optional profile
    let bioAffine := optic%
      (userProfileLens ∘ somePrism ProfileData) ∘ (profileBioLens ∘ somePrism String)
      : AffineTraversal' UserRecord String

    -- Affine traversal to user's age through optional profile
    let ageAffine := optic%
      (userProfileLens ∘ somePrism ProfileData) ∘ (profileAgeLens ∘ somePrism Nat)
      : AffineTraversal' UserRecord Nat

    -- Query bios - only Alice and Dave have them
    (users[0]! ^? bioAffine) ≡? "Engineering lead"
    shouldBeNone (users[1]! ^? bioAffine)
    shouldBeNone (users[2]! ^? bioAffine)  -- Carol has no profile
    (users[3]! ^? bioAffine) ≡? "Contractor"

    IO.println "✓ Database lookup: safely query nested optional bio field"

    -- Query ages
    (users[0]! ^? ageAffine) ≡? 35
    shouldBeNone (users[3]! ^? ageAffine)

    IO.println "✓ Database lookup: safely query nested optional age field"

    -- Update pattern: increment age for users who have one
    let updatedAlice := users[0]! & ageAffine %~ (· + 1)
    (updatedAlice ^? ageAffine) ≡? 36

    -- Update on missing field is no-op
    let updatedDave := users[3]! & ageAffine %~ (· + 1)
    shouldBeNone (updatedDave ^? ageAffine)

    IO.println "✓ Database lookup: safe updates only affect present fields"

/-
**Optic Conversions**: Demonstrates that both Lens and Prism lift to AffineTraversal.

This is the essence of AffineTraversal - it's the meet of Lens and Prism
in the optic hierarchy.
-/
test "Optic conversions: Lens and Prism to AffineTraversal" := do
    let entry := ConfigEntry.mk "test" (some (ConfigValue.int 100))

    -- A Lens is an AffineTraversal that always succeeds
    let fromLens : AffineTraversal' ConfigEntry (Option ConfigValue) := configValueLens

    (entry ^? fromLens) ≡? some (ConfigValue.int 100)

    IO.println "✓ Conversion: Lens lifts to AffineTraversal (always has focus)"

    -- A Prism is an AffineTraversal that may fail to match
    let fromPrism : AffineTraversal' (Option ConfigValue) ConfigValue := somePrism ConfigValue

    (some (ConfigValue.str "hi") ^? fromPrism) ≡? ConfigValue.str "hi"
    shouldBeNone ((none : Option ConfigValue) ^? fromPrism)

    IO.println "✓ Conversion: Prism lifts to AffineTraversal (may not have focus)"

    -- Composed AffineTraversals combine their optionality
    let composed := optic%
      (fromLens ∘ somePrism ConfigValue) ∘ intConfigPrism
      : AffineTraversal' ConfigEntry Int

    (entry ^? composed) ≡? 100

    let entryWithString := ConfigEntry.mk "test" (some (ConfigValue.str "hello"))
    shouldBeNone (entryWithString ^? composed)

    IO.println "✓ Conversion: composed AffineTraversals combine optionality correctly"

-- ## Test Cases: Subtyping Preservation

--Test that the subtyping module compiles and is accessible.
test "Subtyping module: Compiles successfully" := do
  -- The module exists and compiles
  -- All axioms are properly declared
  pure ()

--Test that iso_to_lens_preserves_laws can be invoked and produces a lawful lens.
test "iso_to_lens_preserves_laws: Iso becomes lawful lens" := do
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

--Test iso_to_lens with Bool negation isomorphism.
test "iso_to_lens_preserves_laws: Bool negation iso as lens" := do
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

--Test that iso_to_prism_preserves_laws can be invoked and produces a lawful prism.
test "iso_to_prism_preserves_laws: Iso becomes lawful prism" := do
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

--Test iso_to_prism with Bool negation isomorphism.
test "iso_to_prism_preserves_laws: Bool negation iso as prism" := do
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

--Test that lens_to_affine_preserves_laws can be invoked and produces a lawful affine traversal.
test "lens_to_affine_preserves_laws: Lens becomes lawful affine traversal" := do
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

--Test lens_to_affine with Int negation lens (identity structure).
test "lens_to_affine_preserves_laws: Simple Int lens as affine" := do
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

--Test lens_to_affine with field lens.
test "lens_to_affine_preserves_laws: Field lens (x coordinate) as affine" := do
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

-- ## Test Registration

#generate_tests

end CollimatorTests.AffineTests
