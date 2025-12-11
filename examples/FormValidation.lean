import Collimator.Prelude

/-!
# Form Validation with Prisms

This example demonstrates using prisms for type-safe form validation,
where prisms act as validators that either succeed with a validated value
or fail with the original input.
-/

open Collimator
open scoped Collimator.Operators

/-! ## Validation Prisms -/

/-- Prism for non-empty strings -/
def nonEmpty : Prism' String String :=
  prismFromPartial
    (fun s => if s.isEmpty then none else some s)
    _root_.id

/-- Prism for strings with minimum length -/
def minLength (n : Nat) : Prism' String String :=
  prismFromPartial
    (fun s => if s.length >= n then some s else none)
    _root_.id

/-- Prism for strings with maximum length -/
def maxLength (n : Nat) : Prism' String String :=
  prismFromPartial
    (fun s => if s.length <= n then some s else none)
    _root_.id

/-- Prism for strings matching a simple pattern (contains substring) -/
def containsChar (c : Char) : Prism' String String :=
  prismFromPartial
    (fun s => if s.any (· == c) then some s else none)
    _root_.id

/-- Prism for valid email (simplified: must contain @) -/
def validEmail : Prism' String String :=
  prismFromPartial
    (fun s => if s.containsSubstr "@" && s.length > 3 then some s else none)
    _root_.id

/-- Prism for integers in a range -/
def inRange (lo hi : Int) : Prism' Int Int :=
  prismFromPartial
    (fun n => if lo <= n && n <= hi then some n else none)
    _root_.id

/-- Prism for positive integers -/
def positive : Prism' Int Int :=
  prismFromPartial
    (fun n => if n > 0 then some n else none)
    _root_.id

/-- Prism for non-negative integers -/
def nonNegative : Prism' Int Int :=
  prismFromPartial
    (fun n => if n >= 0 then some n else none)
    _root_.id

/-- Parse string to Int -/
def parseInt : Prism' String Int :=
  prismFromPartial
    (fun s => s.toInt?)
    toString

/-! ## Form Data Types -/

structure RawFormData where
  name : String
  email : String
  age : String  -- Raw string input
  password : String
  confirmPassword : String
  deriving Repr

structure ValidatedForm where
  name : String
  email : String
  age : Int
  password : String
  deriving Repr

/-! ## Form Lenses -/

def formName : Lens' RawFormData String := lens' (·.name) (fun f n => { f with name := n })
def formEmail : Lens' RawFormData String := lens' (·.email) (fun f e => { f with email := e })
def formAge : Lens' RawFormData String := lens' (·.age) (fun f a => { f with age := a })
def formPassword : Lens' RawFormData String := lens' (·.password) (fun f p => { f with password := p })
def formConfirm : Lens' RawFormData String := lens' (·.confirmPassword) (fun f c => { f with confirmPassword := c })

/-! ## Validation Paths -/

-- Composed validation: name must be non-empty and max 50 chars
def validName : AffineTraversal' RawFormData String :=
  formName ∘ nonEmpty ∘ maxLength 50

-- Email validation
def validEmailField : AffineTraversal' RawFormData String :=
  formEmail ∘ validEmail

-- Age validation: parse to int, must be 0-150
def validAgeField : AffineTraversal' RawFormData Int :=
  formAge ∘ parseInt ∘ inRange 0 150

-- Password validation: min 8 chars
def validPassword : AffineTraversal' RawFormData String :=
  formPassword ∘ minLength 8

/-! ## Validation Functions -/

/-- Result of validation with error messages -/
inductive ValidationResult (α : Type) where
  | ok : α → ValidationResult α
  | errors : List String → ValidationResult α
  deriving Repr

/-- Validate a single field with custom error message -/
def validateField {s a : Type} (path : AffineTraversal' s a) (errMsg : String)
    (form : s) : ValidationResult a :=
  match form ^? path with
  | some v => .ok v
  | none => .errors [errMsg]

/-- Combine validation results -/
def combine {a b c : Type} (f : a → b → c)
    (r1 : ValidationResult a) (r2 : ValidationResult b) : ValidationResult c :=
  match r1, r2 with
  | .ok a, .ok b => .ok (f a b)
  | .errors e1, .errors e2 => .errors (e1 ++ e2)
  | .errors e, _ => .errors e
  | _, .errors e => .errors e

/-- Validate the entire form -/
def validateForm (form : RawFormData) : ValidationResult ValidatedForm :=
  let nameResult := validateField validName "Name is required and must be at most 50 characters" form
  let emailResult := validateField validEmailField "Please enter a valid email address" form
  let ageResult := validateField validAgeField "Age must be a number between 0 and 150" form
  let pwResult := validateField validPassword "Password must be at least 8 characters" form

  -- Check password confirmation separately
  let pwMatch := if form.password == form.confirmPassword
    then ValidationResult.ok form.password
    else ValidationResult.errors ["Passwords do not match"]

  -- Combine all validations
  match nameResult, emailResult, ageResult, pwResult, pwMatch with
  | .ok name, .ok email, .ok age, .ok pw, .ok _ =>
    .ok { name, email, age, password := pw }
  | _, _, _, _, _ =>
    let allErrors :=
      (match nameResult with | .errors e => e | _ => []) ++
      (match emailResult with | .errors e => e | _ => []) ++
      (match ageResult with | .errors e => e | _ => []) ++
      (match pwResult with | .errors e => e | _ => []) ++
      (match pwMatch with | .errors e => e | _ => [])
    .errors allErrors

/-! ## Sanitization -/

/-- Trim whitespace from all string fields -/
def sanitizeForm (form : RawFormData) : RawFormData :=
  form
    & formName %~ String.trim
    & formEmail %~ String.trim
    & formAge %~ String.trim

/-! ## Example Usage -/

def examples : IO Unit := do
  IO.println "=== Form Validation Examples ==="
  IO.println ""

  -- Valid form
  let validForm : RawFormData := {
    name := "Alice Smith"
    email := "alice@example.com"
    age := "30"
    password := "securePassword123"
    confirmPassword := "securePassword123"
  }

  IO.println "Testing valid form:"
  match validateForm validForm with
  | .ok v => IO.println s!"  Success: {repr v}"
  | .errors e => IO.println s!"  Errors: {e}"
  IO.println ""

  -- Invalid form - multiple errors
  let invalidForm : RawFormData := {
    name := ""
    email := "not-an-email"
    age := "abc"
    password := "short"
    confirmPassword := "different"
  }

  IO.println "Testing invalid form:"
  match validateForm invalidForm with
  | .ok v => IO.println s!"  Success: {repr v}"
  | .errors e =>
    IO.println "  Errors:"
    for err in e do
      IO.println s!"    - {err}"
  IO.println ""

  -- Partial validation with preview
  IO.println "Individual field validation:"
  IO.println s!"  Valid name in validForm: {validForm ^? validName}"
  IO.println s!"  Valid name in invalidForm: {invalidForm ^? validName}"
  IO.println s!"  Valid age in validForm: {validForm ^? validAgeField}"
  IO.println s!"  Valid age in invalidForm: {invalidForm ^? validAgeField}"
  IO.println ""

  -- Sanitization
  let messyForm : RawFormData := {
    name := "  John Doe  "
    email := " john@example.com "
    age := " 25 "
    password := "password123"
    confirmPassword := "password123"
  }

  IO.println "Before sanitization:"
  IO.println s!"  Name: '{messyForm.name}'"
  IO.println s!"  Email: '{messyForm.email}'"

  let cleanForm := sanitizeForm messyForm
  IO.println "After sanitization:"
  IO.println s!"  Name: '{cleanForm.name}'"
  IO.println s!"  Email: '{cleanForm.email}'"
  IO.println ""

  -- Using prisms for safe parsing
  IO.println "Parsing examples:"
  IO.println s!"  Parse '42': {"42" ^? parseInt}"
  IO.println s!"  Parse 'abc': {"abc" ^? parseInt}"
  let parseAndValidate : Prism' String Int := parseInt ∘ inRange 0 150
  IO.println s!"  Parse and validate '25' (0-150): {"25" ^? parseAndValidate}"
  IO.println s!"  Parse and validate '200' (0-150): {"200" ^? parseAndValidate}"

-- #eval examples
