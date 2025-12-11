import Collimator.Optics
import Collimator.Combinators
import Collimator.Operators
import CollimatorTests.Framework

namespace CollimatorTests.AdvancedShowcase.AffineWizardry

open Collimator
open Collimator.Combinators
open Collimator.AffineTraversalOps
open CollimatorTests

open scoped Collimator.Operators

testSuite "Affine Wizardry"

/-!
# Affine Traversal Wizardry

Demonstrate the power of AffineTraversals (zero-or-one focus):
- Safe partial access without Maybe/Option wrapper overhead
- Composition of Lens + Prism yielding AffineTraversal
- Short-circuiting behavior on missing focuses
- Use cases: database lookups, map access, optional record fields
-/

-- ## Data Structures

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

/-- Nested optional container for testing deep optional access -/
structure Container (α : Type) : Type where
  value : Option α
  deriving BEq, Repr, Inhabited

-- ## Lenses (all at Type level to avoid universe issues)

def configValueLens : Lens' ConfigEntry (Option ConfigValue) := fieldLens% ConfigEntry value

def userEmailLens : Lens' UserRecord (Option String) := fieldLens% UserRecord email

def userProfileLens : Lens' UserRecord (Option ProfileData) := fieldLens% UserRecord profile

def profileBioLens : Lens' ProfileData (Option String) := fieldLens% ProfileData bio

def profileAgeLens : Lens' ProfileData (Option Nat) := fieldLens% ProfileData age

def containerValueLens (α : Type) : Lens' (Container α) (Option α) := fieldLens% Container value

-- ## Prisms

def somePrism (α : Type) : Prism' (Option α) α := ctorPrism% Option.some

def strConfigPrism : Prism' ConfigValue String := ctorPrism% ConfigValue.str

def intConfigPrism : Prism' ConfigValue Int := ctorPrism% ConfigValue.int

def boolConfigPrism : Prism' ConfigValue Bool := ctorPrism% ConfigValue.bool

-- ## Test Cases

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

-- ## Test Registration

#generate_tests

end CollimatorTests.AdvancedShowcase.AffineWizardry
