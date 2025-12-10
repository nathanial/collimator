import Collimator.Optics.Prism
import Collimator.Instances.Sum
import Collimator.Instances.Option
import Collimator.Combinators.Composition
import Collimator.Combinators.Operators
import Collimator.Poly
import CollimatorTests.Framework

namespace CollimatorTests.AdvancedShowcase.PrismMagic

open Collimator
open Collimator.Poly
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

def resultOkPrism (α : Type) : Prism' (Result α) α :=
  prism (fun a => Result.ok a)
        (fun r => match r with
         | Result.ok a => Sum.inr a
         | Result.err e => Sum.inl (Result.err e))

def resultErrPrism (α : Type) : Prism' (Result α) String :=
  prism (fun e => Result.err e)
        (fun r => match r with
         | Result.err e => Sum.inr e
         | Result.ok a => Sum.inl (Result.ok a))

def jsonNullPrism : Prism' JsonValue Unit :=
  prism (fun _ => JsonValue.null)
        (fun v => match v with
         | JsonValue.null => Sum.inr ()
         | other => Sum.inl other)

def jsonBoolPrism : Prism' JsonValue Bool :=
  prism (fun b => JsonValue.bool b)
        (fun v => match v with
         | JsonValue.bool b => Sum.inr b
         | other => Sum.inl other)

def jsonNumPrism : Prism' JsonValue Int :=
  prism (fun n => JsonValue.num n)
        (fun v => match v with
         | JsonValue.num n => Sum.inr n
         | other => Sum.inl other)

def jsonStrPrism : Prism' JsonValue String :=
  prism (fun s => JsonValue.str s)
        (fun v => match v with
         | JsonValue.str s => Sum.inr s
         | other => Sum.inl other)

def jsonArrPrism : Prism' JsonValue (List JsonValue) :=
  prism (fun arr => JsonValue.arr arr)
        (fun v => match v with
         | JsonValue.arr arr => Sum.inr arr
         | other => Sum.inl other)

def jsonObjPrism : Prism' JsonValue (List (String × JsonValue)) :=
  prism (fun obj => JsonValue.obj obj)
        (fun v => match v with
         | JsonValue.obj obj => Sum.inr obj
         | other => Sum.inl other)

def httpSuccessPrism : Prism' HttpStatus Nat :=
  prism (fun code => HttpStatus.success code)
        (fun s => match s with
         | HttpStatus.success code => Sum.inr code
         | other => Sum.inl other)

def httpClientErrPrism : Prism' HttpStatus Nat :=
  prism (fun code => HttpStatus.clientErr code)
        (fun s => match s with
         | HttpStatus.clientErr code => Sum.inr code
         | other => Sum.inl other)

def httpServerErrPrism : Prism' HttpStatus Nat :=
  prism (fun code => HttpStatus.serverErr code)
        (fun s => match s with
         | HttpStatus.serverErr code => Sum.inr code
         | other => Sum.inl other)

def cliFlagPrism : Prism' CliArg String :=
  prism (fun name => CliArg.flag name)
        (fun arg => match arg with
         | CliArg.flag name => Sum.inr name
         | other => Sum.inl other)

def cliOptionPrism : Prism' CliArg (String × String) :=
  prism (fun (name, val) => CliArg.option name val)
        (fun arg => match arg with
         | CliArg.option name val => Sum.inr (name, val)
         | other => Sum.inl other)

def cliPositionalPrism : Prism' CliArg String :=
  prism (fun val => CliArg.positional val)
        (fun arg => match arg with
         | CliArg.positional val => Sum.inr val
         | other => Sum.inl other)

def authAuthenticatedPrism : Prism' AuthState (String × Nat) :=
  prism (fun (user, perms) => AuthState.authenticated user perms)
        (fun s => match s with
         | AuthState.authenticated user perms => Sum.inr (user, perms)
         | other => Sum.inl other)

def authPendingPrism : Prism' AuthState String :=
  prism (fun token => AuthState.pending token)
        (fun s => match s with
         | AuthState.pending token => Sum.inr token
         | other => Sum.inl other)

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
    let _jsonBool := JsonValue.bool true
    let _jsonNull := JsonValue.null

    -- Successful preview extracts the value
    let strResult := preview' jsonStrPrism jsonStr
    if strResult != some "hello" then
      throw (IO.userError s!"Expected Some hello, got {repr strResult}")

    -- Failed preview returns None (type mismatch)
    let numAsStr := preview' jsonStrPrism jsonNum
    if numAsStr != none then
      throw (IO.userError s!"Expected None for num→str preview, got {repr numAsStr}")

    IO.println "✓ Pattern matching: preview extracts matching constructors"

    -- HTTP status categorization
    let ok200 := HttpStatus.success 200
    let notFound := HttpStatus.clientErr 404
    let _serverDown := HttpStatus.serverErr 503

    let isSuccess := preview' httpSuccessPrism ok200
    if isSuccess != some 200 then
      throw (IO.userError s!"Expected Some 200 for success, got {repr isSuccess}")

    let successFromClient := preview' httpSuccessPrism notFound
    if successFromClient != none then
      throw (IO.userError s!"Expected None for client error, got {repr successFromClient}")

    IO.println "✓ Pattern matching: HTTP status categorization"

    -- CLI argument parsing
    let args : List CliArg := [
      CliArg.flag "verbose",
      CliArg.option "output" "file.txt",
      CliArg.positional "input.txt"
    ]

    -- Find all flags
    let flags := args.filterMap (fun a => preview' cliFlagPrism a)
    if flags != ["verbose"] then
      throw (IO.userError s!"Expected [verbose], got {repr flags}")

    -- Find all options
    let options := args.filterMap (fun a => preview' cliOptionPrism a)
    if options != [("output", "file.txt")] then
      throw (IO.userError s!"Expected [(output, file.txt)], got {repr options}")

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
    let strVal := review' jsonStrPrism "constructed"
    if strVal != JsonValue.str "constructed" then
      throw (IO.userError s!"Expected str 'constructed', got {repr strVal}")

    let numVal := review' jsonNumPrism 99
    if numVal != JsonValue.num 99 then
      throw (IO.userError s!"Expected num 99, got {repr numVal}")

    let arrVal := review' jsonArrPrism [JsonValue.num 1, JsonValue.num 2]
    if arrVal != JsonValue.arr [JsonValue.num 1, JsonValue.num 2] then
      throw (IO.userError s!"Expected array, got {repr arrVal}")

    IO.println "✓ Construction: review builds JSON values"

    -- Build HTTP responses
    let success := review' httpSuccessPrism 200
    if success != HttpStatus.success 200 then
      throw (IO.userError s!"Expected success 200, got {repr success}")

    let notFound := review' httpClientErrPrism 404
    if notFound != HttpStatus.clientErr 404 then
      throw (IO.userError s!"Expected clientErr 404, got {repr notFound}")

    IO.println "✓ Construction: review builds HTTP status codes"

    -- Build CLI arguments
    let flag := review' cliFlagPrism "debug"
    if flag != CliArg.flag "debug" then
      throw (IO.userError s!"Expected flag debug, got {repr flag}")

    let opt := review' cliOptionPrism ("config", "app.yaml")
    if opt != CliArg.option "config" "app.yaml" then
      throw (IO.userError s!"Expected option config app.yaml, got {repr opt}")

    IO.println "✓ Construction: review builds CLI arguments"

    -- Build auth states
    let auth := review' authAuthenticatedPrism ("alice", 7)
    if auth != AuthState.authenticated "alice" 7 then
      throw (IO.userError s!"Expected authenticated alice, got {repr auth}")

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

    let validPos := preview' positivePrism 42
    if validPos != some 42 then
      throw (IO.userError s!"Expected Some 42 for positive, got {repr validPos}")

    let invalidPos := preview' positivePrism (-5)
    if invalidPos != none then
      throw (IO.userError s!"Expected None for negative, got {repr invalidPos}")

    let zeroPos := preview' positivePrism 0
    if zeroPos != none then
      throw (IO.userError s!"Expected None for zero, got {repr zeroPos}")

    IO.println "✓ Validation: positive integer prism"

    -- A prism that validates non-empty strings
    let nonEmptyPrism : Prism' String String :=
      prism (fun s => s)
            (fun s => if s.length > 0 then Sum.inr s else Sum.inl s)

    let validStr := preview' nonEmptyPrism "hello"
    if validStr != some "hello" then
      throw (IO.userError s!"Expected Some hello, got {repr validStr}")

    let emptyStr := preview' nonEmptyPrism ""
    if emptyStr != none then
      throw (IO.userError s!"Expected None for empty string, got {repr emptyStr}")

    IO.println "✓ Validation: non-empty string prism"

    -- A prism for valid percentages (0-100)
    let percentPrism : Prism' Nat Nat :=
      prism (fun n => n)
            (fun n => if n <= 100 then Sum.inr n else Sum.inl n)

    let valid50 := preview' percentPrism 50
    if valid50 != some 50 then
      throw (IO.userError s!"Expected Some 50, got {repr valid50}")

    let valid100 := preview' percentPrism 100
    if valid100 != some 100 then
      throw (IO.userError s!"Expected Some 100, got {repr valid100}")

    let invalid150 := preview' percentPrism 150
    if invalid150 != none then
      throw (IO.userError s!"Expected None for 150%, got {repr invalid150}")

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
    let innerValuePrism := composePrism (resultOkPrism (Result Int)) (resultOkPrism Int)

    let innerOk := preview' innerValuePrism nestedOk
    if innerOk != some 42 then
      throw (IO.userError s!"Expected Some 42 for nested ok, got {repr innerOk}")

    let innerFromErr := preview' innerValuePrism nestedErr
    if innerFromErr != none then
      throw (IO.userError s!"Expected None for inner error, got {repr innerFromErr}")

    let innerFromOuter := preview' innerValuePrism outerErr
    if innerFromOuter != none then
      throw (IO.userError s!"Expected None for outer error, got {repr innerFromOuter}")

    IO.println "✓ Composition: nested Result prisms"

    -- JSON array containing numbers
    let jsonArray := JsonValue.arr [JsonValue.num 1, JsonValue.num 2, JsonValue.num 3]
    let jsonNotArray := JsonValue.str "not an array"

    -- First extract the array, then we can process its elements
    let arrResult := preview' jsonArrPrism jsonArray
    if arrResult != some [JsonValue.num 1, JsonValue.num 2, JsonValue.num 3] then
      throw (IO.userError s!"Expected array of nums, got {repr arrResult}")

    let notArrResult := preview' jsonArrPrism jsonNotArray
    if notArrResult != none then
      throw (IO.userError s!"Expected None for non-array, got {repr notArrResult}")

    IO.println "✓ Composition: JSON array extraction"

    -- Build nested structure using review
    let innerResult := review' (resultOkPrism Int) 100
    let outerResult := review' (resultOkPrism (Result Int)) innerResult
    if outerResult != Result.ok (Result.ok 100) then
      throw (IO.userError s!"Expected nested ok 100, got {repr outerResult}")

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
    let successes := results.filterMap (fun r => preview' (resultOkPrism Int) r)
    if successes != [10, 20, 30] then
      throw (IO.userError s!"Expected [10, 20, 30], got {repr successes}")

    IO.println "✓ Error handling: extract all successes"

    -- Extract all error messages
    let errors := results.filterMap (fun r => preview' (resultErrPrism Int) r)
    if errors != ["parse error", "validation error"] then
      throw (IO.userError s!"Expected error messages, got {repr errors}")

    IO.println "✓ Error handling: extract all errors"

    -- Count successes and failures
    let numSuccesses := results.filter (fun r =>
      match preview' (resultOkPrism Int) r with
      | some _ => true
      | none => false
    ) |>.length
    if numSuccesses != 3 then
      throw (IO.userError s!"Expected 3 successes, got {numSuccesses}")

    let numErrors := results.filter (fun r =>
      match preview' (resultErrPrism Int) r with
      | some _ => true
      | none => false
    ) |>.length
    if numErrors != 2 then
      throw (IO.userError s!"Expected 2 errors, got {numErrors}")

    IO.println "✓ Error handling: count successes and failures"

    -- Transform only successful values (keeping errors unchanged)
    -- This simulates map over the success case
    let doubled := results.map (fun r =>
      match preview' (resultOkPrism Int) r with
      | some n => review' (resultOkPrism Int) (n * 2)
      | none => r  -- Keep errors unchanged
    )
    let doubledSuccesses := doubled.filterMap (fun r => preview' (resultOkPrism Int) r)
    if doubledSuccesses != [20, 40, 60] then
      throw (IO.userError s!"Expected [20, 40, 60], got {repr doubledSuccesses}")

    IO.println "✓ Error handling: map over success values"
}

/--
**Sum and Option Prisms**: Working with standard library types.

Demonstrates prisms for Lean's built-in Sum and Option types.
-/
def case_sumOptionPrisms : TestCase := {
  name := "Sum and Option type prisms",
  run := do
    -- Option prisms
    let somePrism (α : Type) : Prism' (Option α) α :=
      prism (fun a => some a)
            (fun o => match o with
             | some a => Sum.inr a
             | none => Sum.inl none)

    let someVal : Option Int := some 42
    let noneVal : Option Int := none

    let fromSome := preview' (somePrism Int) someVal
    if fromSome != some 42 then
      throw (IO.userError s!"Expected Some 42, got {repr fromSome}")

    let fromNone := preview' (somePrism Int) noneVal
    if fromNone != none then
      throw (IO.userError s!"Expected None, got {repr fromNone}")

    let builtSome := review' (somePrism Int) 99
    if builtSome != some 99 then
      throw (IO.userError s!"Expected Some 99, got {repr builtSome}")

    IO.println "✓ Sum/Option: Option some prism"

    -- Sum prisms
    let leftPrism (α β : Type) : Prism' (Sum α β) α :=
      prism (fun a => Sum.inl a)
            (fun s => match s with
             | Sum.inl a => Sum.inr a
             | Sum.inr b => Sum.inl (Sum.inr b))

    let rightPrism (α β : Type) : Prism' (Sum α β) β :=
      prism (fun b => Sum.inr b)
            (fun s => match s with
             | Sum.inr b => Sum.inr b
             | Sum.inl a => Sum.inl (Sum.inl a))

    let leftVal : Sum String Int := Sum.inl "error"
    let rightVal : Sum String Int := Sum.inr 42

    let extractLeft := preview' (leftPrism String Int) leftVal
    if extractLeft != some "error" then
      throw (IO.userError s!"Expected Some error, got {repr extractLeft}")

    let extractRight := preview' (rightPrism String Int) rightVal
    if extractRight != some 42 then
      throw (IO.userError s!"Expected Some 42 from right, got {repr extractRight}")

    let buildLeft := review' (leftPrism String Int) "new error"
    if buildLeft != Sum.inl "new error" then
      throw (IO.userError s!"Expected inl new error, got {repr buildLeft}")

    IO.println "✓ Sum/Option: Sum left/right prisms"
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
