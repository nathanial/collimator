import Collimator.Optics
import Collimator.Instances
import Collimator.Combinators
import Collimator.Operators
import CollimatorTests.Framework

namespace CollimatorTests.AdvancedShowcase.PrismMagic

open Collimator
open Collimator.Combinators
open CollimatorTests

open scoped Collimator.Operators

/-!
# Prism Building/Review Magic

Showcase the dual nature of prisms:
- Pattern matching (preview): Safely extract from sum types
- Construction (review): Build values from parts
- Custom prisms for validation, parsing, and smart constructors
- Prism composition for nested sum types
- Error handling patterns with Either/Sum
-/

-- ## Data Types

/-- Result type for operations that can fail with an error message -/
inductive Result (α : Type) : Type where
  | ok : α → Result α
  | err : String → Result α
  deriving BEq, Repr, Inhabited

/-- A JSON-like value type -/
inductive JsonValue : Type where
  | null : JsonValue
  | bool : Bool → JsonValue
  | num : Int → JsonValue
  | str : String → JsonValue
  | arr : List JsonValue → JsonValue
  | obj : List (String × JsonValue) → JsonValue
  deriving BEq, Repr, Inhabited

/-- HTTP response codes categorized by type -/
inductive HttpStatus : Type where
  | info : Nat → HttpStatus      -- 1xx
  | success : Nat → HttpStatus   -- 2xx
  | redirect : Nat → HttpStatus  -- 3xx
  | clientErr : Nat → HttpStatus -- 4xx
  | serverErr : Nat → HttpStatus -- 5xx
  deriving BEq, Repr, Inhabited

/-- Parsed command-line argument -/
inductive CliArg : Type where
  | flag : String → CliArg         -- --verbose
  | option : String → String → CliArg  -- --output file.txt
  | positional : String → CliArg   -- filename
  deriving BEq, Repr, Inhabited

/-- Authentication state -/
inductive AuthState : Type where
  | anonymous : AuthState
  | pending : String → AuthState   -- pending with token
  | authenticated : String → Nat → AuthState  -- user, permissions
  deriving BEq, Repr, Inhabited

-- ## Prisms for Pattern Matching
-- Using ctorPrism% macro for concise prism definitions

def resultOkPrism (α : Type) : Prism' (Result α) α := ctorPrism% Result.ok
def resultErrPrism (α : Type) : Prism' (Result α) String := ctorPrism% Result.err

def jsonNullPrism : Prism' JsonValue Unit := ctorPrism% JsonValue.null
def jsonBoolPrism : Prism' JsonValue Bool := ctorPrism% JsonValue.bool
def jsonNumPrism : Prism' JsonValue Int := ctorPrism% JsonValue.num
def jsonStrPrism : Prism' JsonValue String := ctorPrism% JsonValue.str
def jsonArrPrism : Prism' JsonValue (List JsonValue) := ctorPrism% JsonValue.arr
def jsonObjPrism : Prism' JsonValue (List (String × JsonValue)) := ctorPrism% JsonValue.obj

def httpInfoPrism : Prism' HttpStatus Nat := ctorPrism% HttpStatus.info
def httpSuccessPrism : Prism' HttpStatus Nat := ctorPrism% HttpStatus.success
def httpRedirectPrism : Prism' HttpStatus Nat := ctorPrism% HttpStatus.redirect
def httpClientErrPrism : Prism' HttpStatus Nat := ctorPrism% HttpStatus.clientErr
def httpServerErrPrism : Prism' HttpStatus Nat := ctorPrism% HttpStatus.serverErr

def cliFlagPrism : Prism' CliArg String := ctorPrism% CliArg.flag
def cliOptionPrism : Prism' CliArg (String × String) := ctorPrism% CliArg.option
def cliPositionalPrism : Prism' CliArg String := ctorPrism% CliArg.positional

def authAnonymousPrism : Prism' AuthState Unit := ctorPrism% AuthState.anonymous
def authPendingPrism : Prism' AuthState String := ctorPrism% AuthState.pending
def authAuthenticatedPrism : Prism' AuthState (String × Nat) := ctorPrism% AuthState.authenticated

-- ## Test Cases

/--
**Pattern Matching (Preview)**: Safely extract values from sum types.

Prisms enable type-safe pattern matching that returns Option, eliminating
runtime pattern match failures.
-/
def case_patternMatching : TestCase := {
  name := "Pattern matching with preview",
  run := do
    -- JSON value extraction
    let jsonStr := JsonValue.str "hello"
    let jsonNum := JsonValue.num 42

    -- Successful preview extracts the value
    (jsonStr ^? jsonStrPrism) ≡? "hello"

    -- Failed preview returns None (type mismatch)
    shouldBeNone (jsonNum ^? jsonStrPrism)

    IO.println "✓ Pattern matching: preview extracts matching constructors"

    -- HTTP status categorization
    let ok200 := HttpStatus.success 200
    let notFound := HttpStatus.clientErr 404

    (ok200 ^? httpSuccessPrism) ≡? 200
    shouldBeNone (notFound ^? httpSuccessPrism)

    IO.println "✓ Pattern matching: HTTP status categorization"

    -- CLI argument parsing
    let args : List CliArg := [
      CliArg.flag "verbose",
      CliArg.option "output" "file.txt",
      CliArg.positional "input.txt"
    ]

    -- Find all flags
    let flags := args.filterMap (fun a => a ^? cliFlagPrism)
    flags ≡ ["verbose"]

    -- Find all options
    let options := args.filterMap (fun a => a ^? cliOptionPrism)
    options ≡ [("output", "file.txt")]

    IO.println "✓ Pattern matching: CLI argument parsing"
}

/--
**Construction (Review)**: Build values from parts using prisms.

The review operation is the inverse of preview - it constructs a value
of the sum type from the focused type.
-/
def case_construction : TestCase := {
  name := "Construction with review",
  run := do
    -- Build JSON values
    review' jsonStrPrism "constructed" ≡ JsonValue.str "constructed"
    review' jsonNumPrism 99 ≡ JsonValue.num 99
    review' jsonArrPrism [JsonValue.num 1, JsonValue.num 2] ≡
      JsonValue.arr [JsonValue.num 1, JsonValue.num 2]

    IO.println "✓ Construction: review builds JSON values"

    -- Build HTTP responses
    review' httpSuccessPrism 200 ≡ HttpStatus.success 200
    review' httpClientErrPrism 404 ≡ HttpStatus.clientErr 404

    IO.println "✓ Construction: review builds HTTP status codes"

    -- Build CLI arguments
    review' cliFlagPrism "debug" ≡ CliArg.flag "debug"
    review' cliOptionPrism ("config", "app.yaml") ≡ CliArg.option "config" "app.yaml"

    IO.println "✓ Construction: review builds CLI arguments"

    -- Build auth states
    review' authAuthenticatedPrism ("alice", 7) ≡ AuthState.authenticated "alice" 7

    IO.println "✓ Construction: review builds authentication states"
}

/--
**Validation Prisms**: Custom prisms that validate during construction.

These prisms encode domain constraints - preview only succeeds for valid
values, and review constructs valid values.
-/
def case_validationPrisms : TestCase := {
  name := "Validation prisms for smart constructors",
  run := do
    -- A prism that only matches positive integers
    let positivePrism : Prism' Int Int :=
      prism (fun n => n)  -- review is identity
            (fun n => if n > 0 then Sum.inr n else Sum.inl n)

    (42 ^? positivePrism) ≡? 42
    shouldBeNone (-5 ^? positivePrism)
    shouldBeNone (0 ^? positivePrism)

    IO.println "✓ Validation: positive integer prism"

    -- A prism that validates non-empty strings
    let nonEmptyPrism : Prism' String String :=
      prism (fun s => s)
            (fun s => if s.length > 0 then Sum.inr s else Sum.inl s)

    ("hello" ^? nonEmptyPrism) ≡? "hello"
    shouldBeNone ("" ^? nonEmptyPrism)

    IO.println "✓ Validation: non-empty string prism"

    -- A prism for valid percentages (0-100)
    let percentPrism : Prism' Nat Nat :=
      prism (fun n => n)
            (fun n => if n <= 100 then Sum.inr n else Sum.inl n)

    (50 ^? percentPrism) ≡? 50
    (100 ^? percentPrism) ≡? 100
    shouldBeNone (150 ^? percentPrism)

    IO.println "✓ Validation: percentage prism (0-100)"
}

/--
**Prism Composition**: Compose prisms for nested sum types.

When you have nested sum types (e.g., Result containing Result, or
JSON arrays containing JSON values), compose prisms to reach deep.
-/
def case_prismComposition : TestCase := {
  name := "Prism composition for nested sum types",
  run := do
    -- Nested Result types
    let nestedOk : Result (Result Int) := Result.ok (Result.ok 42)
    let nestedErr : Result (Result Int) := Result.ok (Result.err "inner error")
    let outerErr : Result (Result Int) := Result.err "outer error"

    -- Compose prisms to reach the inner value
    let innerValuePrism : Prism' (Result (Result Int)) Int :=
      resultOkPrism (Result Int) ∘ resultOkPrism Int

    (nestedOk ^? innerValuePrism) ≡? 42
    shouldBeNone (nestedErr ^? innerValuePrism)
    shouldBeNone (outerErr ^? innerValuePrism)

    IO.println "✓ Composition: nested Result prisms"

    -- JSON array containing numbers
    let jsonArray := JsonValue.arr [JsonValue.num 1, JsonValue.num 2, JsonValue.num 3]
    let jsonNotArray := JsonValue.str "not an array"

    -- First extract the array, then we can process its elements
    (jsonArray ^? jsonArrPrism) ≡? [JsonValue.num 1, JsonValue.num 2, JsonValue.num 3]
    shouldBeNone (jsonNotArray ^? jsonArrPrism)

    IO.println "✓ Composition: JSON array extraction"

    -- Build nested structure using review
    let innerResult := review' (resultOkPrism Int) 100
    let outerResult := review' (resultOkPrism (Result Int)) innerResult
    outerResult ≡ Result.ok (Result.ok 100)

    IO.println "✓ Composition: build nested structures with review"
}

/--
**Error Handling Patterns**: Use prisms for Either/Result error handling.

Prisms provide a clean API for working with error types, enabling
safe extraction and transformation of success/error values.
-/
def case_errorHandling : TestCase := {
  name := "Error handling patterns with Result prisms",
  run := do
    let results : List (Result Int) := [
      Result.ok 10,
      Result.err "parse error",
      Result.ok 20,
      Result.err "validation error",
      Result.ok 30
    ]

    -- Extract all successful values
    let successes := results.filterMap (fun r => r ^? (resultOkPrism Int))
    successes ≡ [10, 20, 30]

    IO.println "✓ Error handling: extract all successes"

    -- Extract all error messages
    let errors := results.filterMap (fun r => r ^? (resultErrPrism Int))
    errors ≡ ["parse error", "validation error"]

    IO.println "✓ Error handling: extract all errors"

    -- Count successes and failures
    let numSuccesses := results.filter (fun r =>
      match r ^? (resultOkPrism Int) with
      | some _ => true
      | none => false
    ) |>.length
    numSuccesses ≡ 3

    let numErrors := results.filter (fun r =>
      match r ^? (resultErrPrism Int) with
      | some _ => true
      | none => false
    ) |>.length
    numErrors ≡ 2

    IO.println "✓ Error handling: count successes and failures"

    -- Transform only successful values (keeping errors unchanged)
    -- This simulates map over the success case
    let doubled := results.map (fun r =>
      match r ^? (resultOkPrism Int) with
      | some n => review' (resultOkPrism Int) (n * 2)
      | none => r  -- Keep errors unchanged
    )
    let doubledSuccesses := doubled.filterMap (fun r => r ^? (resultOkPrism Int))
    doubledSuccesses ≡ [20, 40, 60]

    IO.println "✓ Error handling: map over success values"
}

/--
**Sum and Option Prisms**: Working with standard library types.

Demonstrates prisms for Lean's built-in Sum and Option types using library prisms.
-/
def case_sumOptionPrisms : TestCase := {
  name := "Sum and Option type prisms",
  run := do
    -- Use the library's somePrism' from Collimator.Instances.Option
    let someVal : Option Int := some 42
    let noneVal : Option Int := none

    (someVal ^? Instances.Option.somePrism' Int) ≡? 42
    shouldBeNone (noneVal ^? Instances.Option.somePrism' Int)
    review' (Instances.Option.somePrism' Int) 99 ≡ some 99

    IO.println "✓ Sum/Option: Option some prism (from library)"

    -- Use the library's Sum prisms from Collimator.Instances.Sum
    let leftVal : Sum String Int := Sum.inl "error"
    let rightVal : Sum String Int := Sum.inr 42

    (leftVal ^? Instances.Sum.left' String Int) ≡? "error"
    (rightVal ^? Instances.Sum.right' String Int) ≡? 42
    review' (Instances.Sum.left' String Int) "new error" ≡ Sum.inl "new error"

    IO.println "✓ Sum/Option: Sum left/right prisms (from library)"
}

-- ## Test Registration

def cases : List TestCase := [
  case_patternMatching,
  case_construction,
  case_validationPrisms,
  case_prismComposition,
  case_errorHandling,
  case_sumOptionPrisms
]

end CollimatorTests.AdvancedShowcase.PrismMagic
