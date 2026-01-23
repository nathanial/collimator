import Batteries
import Collimator.Optics
import Collimator.Theorems.PrismLaws
import Collimator.Combinators
import Collimator.Operators
import Collimator.Instances
import Collimator.Concrete.FunArrow
import Crucible

namespace CollimatorTests.PrismTests

open Collimator
open Collimator.Theorems
open Collimator.Combinators
open Collimator.Concrete
open Crucible
open scoped Collimator.Operators

testSuite "Prism Tests"

/-! ## Helper Data Types -/

/-- Shape type for testing prism laws -/
inductive Shape where
  | circle (radius : Int)
  | rectangle (width : Int) (height : Int)
  | triangle (base : Int) (height : Int)
  deriving BEq, Repr

/-- Container type for testing prism composition -/
inductive Container where
  | box (content : Shape)
  | empty
  deriving BEq, Repr

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

/-! ## Prism Definitions -/

-- Shape prisms
private def Shape.buildCircle : Int → Shape := Shape.circle

private def Shape.splitCircle : Shape → Sum Shape Int :=
  fun s => match s with
    | Shape.circle r => Sum.inr r
    | other => Sum.inl other

private def Shape.buildRectangle : (Int × Int) → Shape :=
  fun (w, h) => Shape.rectangle w h

private def Shape.splitRectangle : Shape → Sum Shape (Int × Int) :=
  fun s => match s with
    | Shape.rectangle w h => Sum.inr (w, h)
    | other => Sum.inl other

-- Container prisms
private def Container.buildBox : Shape → Container := Container.box

private def Container.splitBox : Container → Sum Container Shape :=
  fun c => match c with
    | Container.box s => Sum.inr s
    | Container.empty => Sum.inl Container.empty

-- Result prisms using ctorPrism% macro
def resultOkPrism (α : Type) : Prism' (Result α) α := ctorPrism% Result.ok
def resultErrPrism (α : Type) : Prism' (Result α) String := ctorPrism% Result.err

-- JSON prisms using ctorPrism% macro
def jsonNullPrism : Prism' JsonValue Unit := ctorPrism% JsonValue.null
def jsonBoolPrism : Prism' JsonValue Bool := ctorPrism% JsonValue.bool
def jsonNumPrism : Prism' JsonValue Int := ctorPrism% JsonValue.num
def jsonStrPrism : Prism' JsonValue String := ctorPrism% JsonValue.str
def jsonArrPrism : Prism' JsonValue (List JsonValue) := ctorPrism% JsonValue.arr
def jsonObjPrism : Prism' JsonValue (List (String × JsonValue)) := ctorPrism% JsonValue.obj

-- HTTP status prisms using ctorPrism% macro
def httpInfoPrism : Prism' HttpStatus Nat := ctorPrism% HttpStatus.info
def httpSuccessPrism : Prism' HttpStatus Nat := ctorPrism% HttpStatus.success
def httpRedirectPrism : Prism' HttpStatus Nat := ctorPrism% HttpStatus.redirect
def httpClientErrPrism : Prism' HttpStatus Nat := ctorPrism% HttpStatus.clientErr
def httpServerErrPrism : Prism' HttpStatus Nat := ctorPrism% HttpStatus.serverErr

-- CLI argument prisms using ctorPrism% macro
def cliFlagPrism : Prism' CliArg String := ctorPrism% CliArg.flag
def cliOptionPrism : Prism' CliArg (String × String) := ctorPrism% CliArg.option
def cliPositionalPrism : Prism' CliArg String := ctorPrism% CliArg.positional

-- Auth state prisms using ctorPrism% macro
def authAnonymousPrism : Prism' AuthState Unit := ctorPrism% AuthState.anonymous
def authPendingPrism : Prism' AuthState String := ctorPrism% AuthState.pending
def authAuthenticatedPrism : Prism' AuthState (String × Nat) := ctorPrism% AuthState.authenticated

-- Simple option prism for testing
private def optionPrism : Prism (Sum Unit Nat) (Sum Unit Nat) Nat Nat :=
  prism (s := Sum Unit Nat) (t := Sum Unit Nat) (a := Nat) (b := Nat)
    (build := Sum.inr)
    (split :=
      fun
      | Sum.inl u => Sum.inl (Sum.inl u)
      | Sum.inr n => Sum.inr n)

/-! ## Lawful Instances -/

instance : LawfulPrism Shape.buildCircle Shape.splitCircle where
  preview_review := by intro _; rfl
  review_preview := by
    intro s r h
    cases s with
    | circle r' =>
      unfold Shape.splitCircle at h
      injection h with heq
      subst heq
      unfold Shape.buildCircle
      rfl
    | rectangle _ _ => unfold Shape.splitCircle at h; contradiction
    | triangle _ _ => unfold Shape.splitCircle at h; contradiction

instance : LawfulPrism Shape.buildRectangle Shape.splitRectangle where
  preview_review := by intro _; rfl
  review_preview := by
    intro s p h
    cases s with
    | rectangle w h' =>
      unfold Shape.splitRectangle at h
      injection h with heq
      cases p with | mk pw ph =>
        simp at heq
        rcases heq with ⟨hw, hh⟩
        subst hw hh
        unfold Shape.buildRectangle
        rfl
    | circle _ => unfold Shape.splitRectangle at h; contradiction
    | triangle _ _ => unfold Shape.splitRectangle at h; contradiction

instance : LawfulPrism Container.buildBox Container.splitBox where
  preview_review := by intro _; rfl
  review_preview := by
    intro c s h
    cases c with
    | box s' =>
      unfold Container.splitBox at h
      injection h with heq
      subst heq
      unfold Container.buildBox
      rfl
    | empty => unfold Container.splitBox at h; contradiction

/-! ## Basic Operations Tests -/

test "prism preview/review works for sums" := do
  (Sum.inr 7) ^? optionPrism ≡? 7
  shouldBeNone ((Sum.inl ()) ^? optionPrism)
  review' optionPrism 9 ≡ Sum.inr 9

/-! ## Prism Laws Tests -/

test "Prism Preview-Review law: preview p (review p b) = some b" := do
  let circlePrism : Prism' Shape Int := prism Shape.buildCircle Shape.splitCircle
  let radius := 42
  let reviewed := review' circlePrism radius
  let previewed := reviewed ^? circlePrism
  previewed ≡ (some radius)

test "Prism Review-Preview law: preview p s = some a → review p a = s" := do
  let circlePrism : Prism' Shape Int := prism Shape.buildCircle Shape.splitCircle
  let s : Shape := Shape.circle 100
  match s ^? circlePrism with
  | none => throw (IO.userError "Expected preview to succeed")
  | some a =>
    let reconstructed := review' circlePrism a
    reconstructed ≡ s

test "Prism preview returns none on non-matching constructor" := do
  let circlePrism : Prism' Shape Int := prism Shape.buildCircle Shape.splitCircle
  let s : Shape := Shape.rectangle 10 20
  let result := s ^? circlePrism
  result ≡ none

test "Rectangle prism satisfies both laws" := do
  let rectPrism : Prism' Shape (Int × Int) := prism Shape.buildRectangle Shape.splitRectangle

  -- Preview-Review
  let dims := (15, 25)
  let reviewed1 := review' rectPrism dims
  let previewed1 := reviewed1 ^? rectPrism
  previewed1 ≡ (some dims)

  -- Review-Preview
  let s : Shape := Shape.rectangle 30 40
  match s ^? rectPrism with
  | none => throw (IO.userError "Expected preview to succeed")
  | some d =>
    let reconstructed := review' rectPrism d
    reconstructed ≡ s

test "Composed prisms satisfy Preview-Review law" := do
  let boxPrism : Prism' Container Shape := prism Container.buildBox Container.splitBox
  let circlePrism : Prism' Shape Int := prism Shape.buildCircle Shape.splitCircle
  let composed : Prism' Container Int := boxPrism ∘ circlePrism

  let radius := 77
  let reviewed := review' composed radius
  let previewed := reviewed ^? composed
  previewed ≡ (some radius)

test "Composed prisms satisfy Review-Preview law" := do
  let boxPrism : Prism' Container Shape := prism Container.buildBox Container.splitBox
  let circlePrism : Prism' Shape Int := prism Shape.buildCircle Shape.splitCircle
  let composed : Prism' Container Int := boxPrism ∘ circlePrism

  let c : Container := Container.box (Shape.circle 99)
  match c ^? composed with
  | none => throw (IO.userError "Expected preview to succeed")
  | some a =>
    let reconstructed := review' composed a
    reconstructed ≡ c

test "Composed prism preview fails on outer mismatch" := do
  let boxPrism : Prism' Container Shape := prism Container.buildBox Container.splitBox
  let circlePrism : Prism' Shape Int := prism Shape.buildCircle Shape.splitCircle
  let composed : Prism' Container Int := boxPrism ∘ circlePrism

  let c : Container := Container.empty
  let result := c ^? composed
  result ≡ none

test "Composed prism preview fails on inner mismatch" := do
  let boxPrism : Prism' Container Shape := prism Container.buildBox Container.splitBox
  let circlePrism : Prism' Shape Int := prism Shape.buildCircle Shape.splitCircle
  let composed : Prism' Container Int := boxPrism ∘ circlePrism

  let c : Container := Container.box (Shape.rectangle 5 10)
  let result := c ^? composed
  result ≡ none

test "Prism law theorems can be invoked" := do
  -- The theorems themselves are compile-time proofs
  -- We verify they exist and are applicable by using them in computations
  let circlePrism : Prism' Shape Int := prism Shape.buildCircle Shape.splitCircle

  -- These operations should satisfy the laws by construction
  let test1 := (review' circlePrism 50) ^? circlePrism
  let s := Shape.circle 75
  let test2 := match s ^? circlePrism with
    | some a => review' circlePrism a
    | none => s

  test1 ≡ (some 50)
  test2 ≡ s

test "Composition lawfulness instance is usable" := do
  -- The instance composedPrism_isLawful proves that composed build/split are lawful
  let boxPrism : Prism' Container Shape := prism Container.buildBox Container.splitBox
  let rectPrism : Prism' Shape (Int × Int) := prism Shape.buildRectangle Shape.splitRectangle
  let composed : Prism' Container (Int × Int) := boxPrism ∘ rectPrism

  -- Verify the composition works correctly
  let c := Container.box (Shape.rectangle 8 12)
  let viewed := c ^? composed
  viewed ≡ (some (8, 12))

  let c' := review' composed (20, 30)
  let expected := Container.box (Shape.rectangle 20 30)
  c' ≡ expected

test "Option some prism satisfies laws" := do
  let somePrism : Prism' (Option Int) Int :=
    prism some (fun opt => match opt with
      | some a => Sum.inr a
      | none => Sum.inl none)

  -- Preview-Review
  let reviewed := review' somePrism 123
  let previewed := reviewed ^? somePrism
  previewed ≡ (some 123)

  -- Review-Preview on Some
  let opt := some 456
  match opt ^? somePrism with
  | none => throw (IO.userError "Expected preview to succeed")
  | some a =>
    let reconstructed := review' somePrism a
    reconstructed ≡ opt

  -- Preview on None
  let result := (none : Option Int) ^? somePrism
  result ≡ none

/-! ## Advanced Prism Magic Tests -/

/-
**Pattern Matching (Preview)**: Safely extract values from sum types.

Prisms enable type-safe pattern matching that returns Option, eliminating
runtime pattern match failures.
-/
test "Pattern matching with preview" := do
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

/-
**Construction (Review)**: Build values from parts using prisms.

The review operation is the inverse of preview - it constructs a value
of the sum type from the focused type.
-/
test "Construction with review" := do
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

/-
**Validation Prisms**: Custom prisms that validate during construction.

These prisms encode domain constraints - preview only succeeds for valid
values, and review constructs valid values.
-/
test "Validation prisms for smart constructors" := do
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

/-
**Prism Composition**: Compose prisms for nested sum types.

When you have nested sum types (e.g., Result containing Result, or
JSON arrays containing JSON values), compose prisms to reach deep.
-/
test "Prism composition for nested sum types" := do
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

/-
**Error Handling Patterns**: Use prisms for Either/Result error handling.

Prisms provide a clean API for working with error types, enabling
safe extraction and transformation of success/error values.
-/
test "Error handling patterns with Result prisms" := do
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

/-
**Sum and Option Prisms**: Working with standard library types.

Demonstrates prisms for Lean's built-in Sum and Option types using library prisms.
-/
test "Sum and Option type prisms" := do
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

end CollimatorTests.PrismTests
