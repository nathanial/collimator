import Crucible
import Collimator.Prelude
import Collimator.Integration

/-!
# Integration Tests

Tests for Collimator's integration utilities with Except, StateM, ReaderM, etc.
-/

open Collimator
open Collimator.Integration
open Collimator.Instances.Option
open Collimator.Instances.List
open Crucible

namespace CollimatorTests.IntegrationTests

testSuite "Integration Tests"

/-! ## Test Data -/

private structure Person where
  name : String
  age : Int
deriving BEq, Repr

private def nameLens : Lens' Person String :=
  lens' (·.name) (fun p n => { p with name := n })

private def ageLens : Lens' Person Int :=
  lens' (·.age) (fun p a => { p with age := a })

/-! ## Except Integration Tests -/

test "validateThrough: valid input passes" := do
  let person := Person.mk "Alice" 25
  let validateName : String → Except String String
    | s => if s.length > 0 then .ok s else .error "empty name"
  let result := validateThrough nameLens validateName person
  match result with
  | .ok _ => pure ()
  | .error e => throw <| IO.userError s!"Unexpected error: {e}"

test "validateThrough: invalid input fails" := do
  let person := Person.mk "" 25
  let validateName : String → Except String String
    | s => if s.length > 0 then .ok s else .error "empty name"
  let result := validateThrough nameLens validateName person
  match result with
  | .ok _ => throw <| IO.userError "Expected error but got success"
  | .error _ => pure ()

test "validateThrough: updates on success" := do
  let person := Person.mk "alice" 25
  let capitalize : String → Except String String
    | s => .ok s.capitalize
  let result := validateThrough nameLens capitalize person
  match result with
  | .ok p => p.name ≡ "Alice"
  | .error e => throw <| IO.userError s!"Unexpected error: {e}"

test "previewOrError: returns value when present" := do
  let opt : Option Int := some 42
  let result := previewOrError (somePrism' Int) "missing" opt
  match result with
  | .ok n => n ≡ 42
  | .error _ => throw <| IO.userError "Expected success"

test "previewOrError: returns error when absent" := do
  let opt : Option Int := none
  let result := previewOrError (somePrism' Int) "missing" opt
  match result with
  | .ok _ => throw <| IO.userError "Expected error"
  | .error e => e ≡ "missing"

test "validateAll: succeeds when all valid" := do
  let nums := [1, 2, 3, 4, 5]
  let validatePositive : Int → Except String Int
    | n => if n > 0 then .ok n else .error "non-positive"
  let result := validateAll traversed validatePositive nums
  match result with
  | .ok ns => ns ≡ [1, 2, 3, 4, 5]
  | .error _ => throw <| IO.userError "Expected success"

test "validateAll: fails on first invalid" := do
  let nums := [1, -2, 3, -4, 5]
  let validatePositive : Int → Except String Int
    | n => if n > 0 then .ok n else .error "non-positive"
  let result := validateAll traversed validatePositive nums
  match result with
  | .ok _ => throw <| IO.userError "Expected error"
  | .error e => e ≡ "non-positive"

/-! ## StateM Integration Tests -/

test "getThrough: reads focused value" := do
  let person := Person.mk "Bob" 30
  let (age, _) := (getThrough ageLens).run person
  age ≡ 30

test "setThrough: writes focused value" := do
  let person := Person.mk "Bob" 30
  let ((), person') := (setThrough ageLens 35).run person
  person'.age ≡ 35

test "overThrough: modifies focused value" := do
  let person := Person.mk "Bob" 30
  let ((), person') := (overThrough ageLens (· + 1)).run person
  person'.age ≡ 31

test "zoom: runs action on focused state" := do
  let person := Person.mk "Bob" 30
  let action : StateM Int Int := do
    let n ← get
    set (n * 2)
    pure n
  let (oldAge, person') := (zoom ageLens action).run person
  oldAge ≡ 30
  person'.age ≡ 60

test "modifyThrough: stateful operation on focus" := do
  let person := Person.mk "Bob" 30
  let bumpAndReturn : StateM Int Int := do
    let n ← get
    set (n + 5)
    pure n
  let (old, person') := (modifyThrough ageLens bumpAndReturn).run person
  old ≡ 30
  person'.age ≡ 35

/-! ## ReaderM Integration Tests -/

test "askThrough: reads focused value from environment" := do
  let person := Person.mk "Carol" 28
  let name : String := (askThrough nameLens).run person
  name ≡ "Carol"

test "localThrough: modifies environment for block" := do
  let person := Person.mk "carol" 28
  let action : ReaderM Person String := askThrough nameLens
  let capitalizedAction := localThrough nameLens String.capitalize action
  let result : String := capitalizedAction.run person
  result ≡ "Carol"

/-! ## Option/Prism Integration Tests -/

test "updateWhenMatches: updates when pattern matches" := do
  let opt : Option Int := some 10
  let result := updateWhenMatches (somePrism' Int) (· * 2) opt
  result ≡ (some 20)

test "updateWhenMatches: no-op when pattern doesn't match" := do
  let opt : Option Int := none
  let result := updateWhenMatches (somePrism' Int) (· * 2) opt
  result ≡ none

test "prismToSum: converts Some to inr" := do
  let opt : Option Int := some 42
  let result := prismToSum (somePrism' Int) opt
  match result with
  | .inr n => n ≡ 42
  | .inl _ => throw <| IO.userError "Expected inr"

test "prismToSum: converts None to inl" := do
  let opt : Option Int := none
  let result := prismToSum (somePrism' Int) opt
  match result with
  | .inl orig => orig ≡ none
  | .inr _ => throw <| IO.userError "Expected inl"

/-! ## Traversal Integration Tests -/

test "mapMaybe: transforms elements selectively" := do
  let nums := [1, 2, 3, 4, 5]
  -- Double only even numbers
  let result := mapMaybe traversed
    (fun n => if n % 2 == 0 then some (n * 2) else none)
    nums
  -- Odd numbers unchanged, even numbers doubled
  result ≡ [1, 4, 3, 8, 5]

test "traverseOption: effectful traversal with Option" := do
  let nums := [2, 4, 6]
  let result := traverseOption traversed
    (fun n => if n % 2 == 0 then some (n / 2) else none)
    nums
  result ≡ (some [1, 2, 3])

test "traverseOption: short-circuits on failure" := do
  let nums := [2, 3, 6]  -- 3 is odd
  let result := traverseOption traversed
    (fun n => if n % 2 == 0 then some (n / 2) else none)
    nums
  result ≡ (none : Option (List Int))

end CollimatorTests.IntegrationTests
