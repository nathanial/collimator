import Collimator.Optics.Affine
import Collimator.Optics.Lens
import Collimator.Optics.Prism
import Collimator.Combinators.Composition
import Collimator.Combinators.Operators
import Collimator.Poly
import CollimatorTests.Framework

namespace CollimatorTests.AdvancedShowcase.AffineWizardry

open Collimator
open Collimator.Poly
open Collimator.Combinators
open Collimator.AffineTraversalOps
open CollimatorTests

open scoped Collimator.Operators

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

def configValueLens : Lens' ConfigEntry (Option ConfigValue) :=
  lens' (fun e => e.value) (fun e v => { e with value := v })

def userEmailLens : Lens' UserRecord (Option String) :=
  lens' (fun u => u.email) (fun u e => { u with email := e })

def userProfileLens : Lens' UserRecord (Option ProfileData) :=
  lens' (fun u => u.profile) (fun u p => { u with profile := p })

def profileBioLens : Lens' ProfileData (Option String) :=
  lens' (fun p => p.bio) (fun p b => { p with bio := b })

def profileAgeLens : Lens' ProfileData (Option Nat) :=
  lens' (fun p => p.age) (fun p a => { p with age := a })

def containerValueLens (α : Type) : Lens' (Container α) (Option α) :=
  lens' (fun c => c.value) (fun c v => { c with value := v })

-- ## Prisms

def somePrism (α : Type) : Prism' (Option α) α :=
  prism (fun a => some a)
        (fun o => match o with
         | some a => Sum.inr a
         | none => Sum.inl none)

def strConfigPrism : Prism' ConfigValue String :=
  prism (fun s => ConfigValue.str s)
        (fun v => match v with
         | ConfigValue.str s => Sum.inr s
         | other => Sum.inl other)

def intConfigPrism : Prism' ConfigValue Int :=
  prism (fun i => ConfigValue.int i)
        (fun v => match v with
         | ConfigValue.int i => Sum.inr i
         | other => Sum.inl other)

def boolConfigPrism : Prism' ConfigValue Bool :=
  prism (fun b => ConfigValue.bool b)
        (fun v => match v with
         | ConfigValue.bool b => Sum.inr b
         | other => Sum.inl other)

-- ## Test Cases

/--
**Safe Partial Access**: Demonstrates accessing optional values safely.

AffineTraversals provide a middle ground between Lens (always present) and
Traversal (zero or more). With AffineTraversal, we know there's at most
one focus, which enables certain optimizations and clearer semantics.
-/
def case_safePartialAccess : TestCase := {
  name := "Safe partial access with AffineTraversal",
  run := do
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
    let emailAffine := composeLensPrism userEmailLens (somePrism String)

    -- Preview safely extracts the value if present
    let aliceEmail := AffineTraversalOps.preview' emailAffine completeUser
    if aliceEmail != some "alice@example.com" then
      throw (IO.userError s!"Expected Some alice@example.com, got {repr aliceEmail}")

    let bobEmail := AffineTraversalOps.preview' emailAffine partialUser
    if bobEmail != some "bob@example.com" then
      throw (IO.userError s!"Expected Some bob@example.com, got {repr bobEmail}")

    let carolEmail := AffineTraversalOps.preview' emailAffine minimalUser
    if carolEmail != none then
      throw (IO.userError s!"Expected None, got {repr carolEmail}")

    IO.println "✓ Safe partial access: preview returns Option based on focus presence"

    -- Set only modifies when focus is present
    let updatedAlice := AffineTraversalOps.set emailAffine "newalice@example.com" completeUser
    if updatedAlice.email != some "newalice@example.com" then
      throw (IO.userError s!"Expected email update, got {repr updatedAlice.email}")

    let updatedCarol := AffineTraversalOps.set emailAffine "carol@example.com" minimalUser
    -- Carol has no email, so set with the affine leaves it unchanged
    if updatedCarol.email != none then
      throw (IO.userError s!"Expected unchanged none email, got {repr updatedCarol.email}")

    IO.println "✓ Safe partial access: set only modifies when focus exists"
}

/--
**Lens + Prism Composition**: Shows how composing Lens with Prism yields AffineTraversal.

This is the canonical way to create AffineTraversals - the composition of a
Lens (which always has a focus) with a Prism (which may or may not match)
creates an optic that focuses on at most one value.
-/
def case_lensPrismComposition : TestCase := {
  name := "Lens + Prism composition yields AffineTraversal",
  run := do
    let entries := [
      ConfigEntry.mk "host" (some (ConfigValue.str "localhost")),
      ConfigEntry.mk "port" (some (ConfigValue.int 8080)),
      ConfigEntry.mk "debug" (some (ConfigValue.bool true)),
      ConfigEntry.mk "timeout" none  -- Missing value
    ]

    -- Lens into Option ConfigValue, then Prism to String
    let strValueAffine :=
      composeAffine
        (composeLensPrism configValueLens (somePrism ConfigValue))
        (AffineTraversalOps.ofPrism strConfigPrism)

    -- Lens into Option ConfigValue, then Prism to Int
    let intValueAffine :=
      composeAffine
        (composeLensPrism configValueLens (somePrism ConfigValue))
        (AffineTraversalOps.ofPrism intConfigPrism)

    -- Preview string values
    let hostValue := AffineTraversalOps.preview' strValueAffine entries[0]!
    if hostValue != some "localhost" then
      throw (IO.userError s!"Expected Some localhost, got {repr hostValue}")

    let portStrValue := AffineTraversalOps.preview' strValueAffine entries[1]!
    if portStrValue != none then  -- port is Int, not String
      throw (IO.userError s!"Expected None for Int value, got {repr portStrValue}")

    IO.println "✓ Lens + Prism: composition correctly filters by type"

    -- Preview int values
    let portIntValue := AffineTraversalOps.preview' intValueAffine entries[1]!
    if portIntValue != some 8080 then
      throw (IO.userError s!"Expected Some 8080, got {repr portIntValue}")

    let hostIntValue := AffineTraversalOps.preview' intValueAffine entries[0]!
    if hostIntValue != none then  -- host is String, not Int
      throw (IO.userError s!"Expected None for String value, got {repr hostIntValue}")

    IO.println "✓ Lens + Prism: type-safe extraction of sum type variants"

    -- Modify string value
    let updatedHost := AffineTraversalOps.over strValueAffine (· ++ ":3000") entries[0]!
    match updatedHost.value with
    | some (ConfigValue.str s) =>
        if s != "localhost:3000" then
          throw (IO.userError s!"Expected localhost:3000, got {s}")
    | _ => throw (IO.userError "Expected string config value")

    -- Trying to modify with wrong prism leaves value unchanged
    let notUpdatedPort := AffineTraversalOps.over strValueAffine (· ++ "!") entries[1]!
    if notUpdatedPort.value != some (ConfigValue.int 8080) then
      throw (IO.userError "Expected port value unchanged")

    IO.println "✓ Lens + Prism: modifications only apply when prism matches"
}

/--
**Short-Circuit Behavior**: Demonstrates that AffineTraversals stop early when focus is missing.

Unlike Traversals that always visit all possible focuses, AffineTraversals
know there's at most one focus, enabling efficient short-circuit evaluation.
-/
def case_shortCircuit : TestCase := {
  name := "Short-circuiting behavior on missing focuses",
  run := do
    -- Deep nested optional structure
    let deepPresent : Container (Container (Container Nat)) :=
      ⟨some ⟨some ⟨some 42⟩⟩⟩

    let midMissing : Container (Container (Container Nat)) :=
      ⟨some ⟨none⟩⟩

    let topMissing : Container (Container (Container Nat)) :=
      ⟨none⟩

    -- Build deep affine traversal through 3 levels of Option
    let level1 := composeLensPrism
      (containerValueLens (Container (Container Nat)))
      (somePrism (Container (Container Nat)))
    let level2 := composeAffine level1 (composeLensPrism
      (containerValueLens (Container Nat))
      (somePrism (Container Nat)))
    let deepAffine := composeAffine level2 (composeLensPrism
      (containerValueLens Nat)
      (somePrism Nat))

    -- All present - we can access the value
    let presentResult := AffineTraversalOps.preview' deepAffine deepPresent
    if presentResult != some 42 then
      throw (IO.userError s!"Expected Some 42, got {repr presentResult}")

    IO.println "✓ Short-circuit: deep access succeeds when all levels present"

    -- Missing in middle - short circuits
    let midResult := AffineTraversalOps.preview' deepAffine midMissing
    if midResult != none then
      throw (IO.userError s!"Expected None for mid-missing, got {repr midResult}")

    IO.println "✓ Short-circuit: stops at first missing level (middle)"

    -- Missing at top - short circuits immediately
    let topResult := AffineTraversalOps.preview' deepAffine topMissing
    if topResult != none then
      throw (IO.userError s!"Expected None for top-missing, got {repr topResult}")

    IO.println "✓ Short-circuit: stops at first missing level (top)"

    -- Modification also short-circuits
    let modifiedPresent := AffineTraversalOps.over deepAffine (· * 2) deepPresent
    let checkModified := AffineTraversalOps.preview' deepAffine modifiedPresent
    if checkModified != some 84 then
      throw (IO.userError s!"Expected Some 84 after modification, got {repr checkModified}")

    let modifiedMissing := AffineTraversalOps.over deepAffine (· * 2) midMissing
    -- Structure unchanged since there's nothing to modify
    if modifiedMissing.value != some ⟨none⟩ then
      throw (IO.userError "Expected structure unchanged")

    IO.println "✓ Short-circuit: over operation also short-circuits on missing focus"
}

/--
**Database Lookup Patterns**: Real-world pattern of accessing optional nested fields.

Shows how AffineTraversals elegantly handle the common database pattern of
records with optional fields and nested optional relationships.
-/
def case_databaseLookup : TestCase := {
  name := "Database lookup patterns with optional fields",
  run := do
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
    let bioAffine :=
      composeAffine
        (composeLensPrism userProfileLens (somePrism ProfileData))
        (composeLensPrism profileBioLens (somePrism String))

    -- Affine traversal to user's age through optional profile
    let ageAffine :=
      composeAffine
        (composeLensPrism userProfileLens (somePrism ProfileData))
        (composeLensPrism profileAgeLens (somePrism Nat))

    -- Query bios - only Alice and Dave have them
    let aliceBio := AffineTraversalOps.preview' bioAffine users[0]!
    if aliceBio != some "Engineering lead" then
      throw (IO.userError s!"Expected Alice's bio, got {repr aliceBio}")

    let bobBio := AffineTraversalOps.preview' bioAffine users[1]!
    if bobBio != none then
      throw (IO.userError s!"Expected None for Bob's bio, got {repr bobBio}")

    let carolBio := AffineTraversalOps.preview' bioAffine users[2]!
    if carolBio != none then
      throw (IO.userError s!"Expected None for Carol's bio (no profile), got {repr carolBio}")

    let daveBio := AffineTraversalOps.preview' bioAffine users[3]!
    if daveBio != some "Contractor" then
      throw (IO.userError s!"Expected Dave's bio, got {repr daveBio}")

    IO.println "✓ Database lookup: safely query nested optional bio field"

    -- Query ages
    let aliceAge := AffineTraversalOps.preview' ageAffine users[0]!
    if aliceAge != some 35 then
      throw (IO.userError s!"Expected Alice's age 35, got {repr aliceAge}")

    let daveAge := AffineTraversalOps.preview' ageAffine users[3]!
    if daveAge != none then
      throw (IO.userError s!"Expected None for Dave's age, got {repr daveAge}")

    IO.println "✓ Database lookup: safely query nested optional age field"

    -- Update pattern: increment age for users who have one
    let updatedAlice := AffineTraversalOps.over ageAffine (· + 1) users[0]!
    let newAliceAge := AffineTraversalOps.preview' ageAffine updatedAlice
    if newAliceAge != some 36 then
      throw (IO.userError s!"Expected updated age 36, got {repr newAliceAge}")

    -- Update on missing field is no-op
    let updatedDave := AffineTraversalOps.over ageAffine (· + 1) users[3]!
    let newDaveAge := AffineTraversalOps.preview' ageAffine updatedDave
    if newDaveAge != none then
      throw (IO.userError s!"Expected age still None, got {repr newDaveAge}")

    IO.println "✓ Database lookup: safe updates only affect present fields"
}

/--
**Optic Conversions**: Demonstrates that both Lens and Prism lift to AffineTraversal.

This is the essence of AffineTraversal - it's the meet of Lens and Prism
in the optic hierarchy.
-/
def case_opticConversions : TestCase := {
  name := "Optic conversions: Lens and Prism to AffineTraversal",
  run := do
    let entry := ConfigEntry.mk "test" (some (ConfigValue.int 100))

    -- A Lens is an AffineTraversal that always succeeds
    let fromLens := AffineTraversalOps.ofLens configValueLens

    let lensPreview := AffineTraversalOps.preview' fromLens entry
    if lensPreview != some (some (ConfigValue.int 100)) then
      throw (IO.userError s!"Expected Some (Some int 100), got {repr lensPreview}")

    IO.println "✓ Conversion: Lens lifts to AffineTraversal (always has focus)"

    -- A Prism is an AffineTraversal that may fail to match
    let fromPrism := AffineTraversalOps.ofPrism (somePrism ConfigValue)

    let prismPreviewSome := AffineTraversalOps.preview' fromPrism (some (ConfigValue.str "hi"))
    if prismPreviewSome != some (ConfigValue.str "hi") then
      throw (IO.userError s!"Expected Some str hi, got {repr prismPreviewSome}")

    let prismPreviewNone := AffineTraversalOps.preview' fromPrism (none : Option ConfigValue)
    if prismPreviewNone != none then
      throw (IO.userError s!"Expected None, got {repr prismPreviewNone}")

    IO.println "✓ Conversion: Prism lifts to AffineTraversal (may not have focus)"

    -- Composed AffineTraversals combine their optionality
    let composed := composeAffine
      (composeAffine fromLens (AffineTraversalOps.ofPrism (somePrism ConfigValue)))
      (AffineTraversalOps.ofPrism intConfigPrism)

    let composedResult := AffineTraversalOps.preview' composed entry
    if composedResult != some 100 then
      throw (IO.userError s!"Expected Some 100, got {repr composedResult}")

    let entryWithString := ConfigEntry.mk "test" (some (ConfigValue.str "hello"))
    let composedNoMatch := AffineTraversalOps.preview' composed entryWithString
    if composedNoMatch != none then
      throw (IO.userError s!"Expected None for string value, got {repr composedNoMatch}")

    IO.println "✓ Conversion: composed AffineTraversals combine optionality correctly"
}

-- ## Test Registration

def cases : List TestCase := [
  case_safePartialAccess,
  case_lensPrismComposition,
  case_shortCircuit,
  case_databaseLookup,
  case_opticConversions
]

end CollimatorTests.AdvancedShowcase.AffineWizardry
