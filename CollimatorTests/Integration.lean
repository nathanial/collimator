import CollimatorTests.Framework
import Collimator.Prelude
import Collimator.Integration

/-!
# Tests for Integration Patterns

Tests for Collimator's integration utilities with Except, StateM, ReaderM, etc.
-/

open Collimator
open Collimator.Integration
open Collimator.Instances.Option
open Collimator.Instances.List
open CollimatorTests

namespace CollimatorTests.Integration

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

def exceptTests : List TestCase := [
  {
    name := "validateThrough: valid input passes"
    run := do
      let person := Person.mk "Alice" 25
      let validateName : String → Except String String
        | s => if s.length > 0 then .ok s else .error "empty name"
      let result := validateThrough nameLens validateName person
      match result with
      | .ok _ => pure ()
      | .error e => throw <| IO.userError s!"Unexpected error: {e}"
  },
  {
    name := "validateThrough: invalid input fails"
    run := do
      let person := Person.mk "" 25
      let validateName : String → Except String String
        | s => if s.length > 0 then .ok s else .error "empty name"
      let result := validateThrough nameLens validateName person
      match result with
      | .ok _ => throw <| IO.userError "Expected error but got success"
      | .error _ => pure ()
  },
  {
    name := "validateThrough: updates on success"
    run := do
      let person := Person.mk "alice" 25
      let capitalize : String → Except String String
        | s => .ok s.capitalize
      let result := validateThrough nameLens capitalize person
      match result with
      | .ok p => ensureEq "capitalized" "Alice" p.name
      | .error e => throw <| IO.userError s!"Unexpected error: {e}"
  },
  {
    name := "previewOrError: returns value when present"
    run := do
      let opt : Option Int := some 42
      let result := previewOrError (somePrism' Int) "missing" opt
      match result with
      | .ok n => ensureEq "extracted" 42 n
      | .error _ => throw <| IO.userError "Expected success"
  },
  {
    name := "previewOrError: returns error when absent"
    run := do
      let opt : Option Int := none
      let result := previewOrError (somePrism' Int) "missing" opt
      match result with
      | .ok _ => throw <| IO.userError "Expected error"
      | .error e => ensureEq "error message" "missing" e
  },
  {
    name := "validateAll: succeeds when all valid"
    run := do
      let nums := [1, 2, 3, 4, 5]
      let validatePositive : Int → Except String Int
        | n => if n > 0 then .ok n else .error "non-positive"
      let result := validateAll traversed validatePositive nums
      match result with
      | .ok ns => ensureEq "unchanged" [1, 2, 3, 4, 5] ns
      | .error _ => throw <| IO.userError "Expected success"
  },
  {
    name := "validateAll: fails on first invalid"
    run := do
      let nums := [1, -2, 3, -4, 5]
      let validatePositive : Int → Except String Int
        | n => if n > 0 then .ok n else .error "non-positive"
      let result := validateAll traversed validatePositive nums
      match result with
      | .ok _ => throw <| IO.userError "Expected error"
      | .error e => ensureEq "error message" "non-positive" e
  }
]

/-! ## StateM Integration Tests -/

def stateTests : List TestCase := [
  {
    name := "getThrough: reads focused value"
    run := do
      let person := Person.mk "Bob" 30
      let (age, _) := (getThrough ageLens).run person
      ensureEq "age" 30 age
  },
  {
    name := "setThrough: writes focused value"
    run := do
      let person := Person.mk "Bob" 30
      let ((), person') := (setThrough ageLens 35).run person
      ensureEq "new age" 35 person'.age
  },
  {
    name := "overThrough: modifies focused value"
    run := do
      let person := Person.mk "Bob" 30
      let ((), person') := (overThrough ageLens (· + 1)).run person
      ensureEq "incremented age" 31 person'.age
  },
  {
    name := "zoom: runs action on focused state"
    run := do
      let person := Person.mk "Bob" 30
      let action : StateM Int Int := do
        let n ← get
        set (n * 2)
        pure n
      let (oldAge, person') := (zoom ageLens action).run person
      ensureEq "old age returned" 30 oldAge
      ensureEq "age doubled" 60 person'.age
  },
  {
    name := "modifyThrough: stateful operation on focus"
    run := do
      let person := Person.mk "Bob" 30
      let bumpAndReturn : StateM Int Int := do
        let n ← get
        set (n + 5)
        pure n
      let (old, person') := (modifyThrough ageLens bumpAndReturn).run person
      ensureEq "returned old value" 30 old
      ensureEq "bumped by 5" 35 person'.age
  }
]

/-! ## ReaderM Integration Tests -/

def readerTests : List TestCase := [
  {
    name := "askThrough: reads focused value from environment"
    run := do
      let person := Person.mk "Carol" 28
      let name := (askThrough nameLens).run person
      ensureEq "name" "Carol" name
  },
  {
    name := "localThrough: modifies environment for block"
    run := do
      let person := Person.mk "carol" 28
      let action : ReaderM Person String := askThrough nameLens
      let capitalizedAction := localThrough nameLens String.capitalize action
      let result := capitalizedAction.run person
      ensureEq "capitalized in block" "Carol" result
  }
]

/-! ## Option/Prism Integration Tests -/

def optionTests : List TestCase := [
  {
    name := "updateWhenMatches: updates when pattern matches"
    run := do
      let opt : Option Int := some 10
      let result := updateWhenMatches (somePrism' Int) (· * 2) opt
      ensureEq "doubled" (some 20) result
  },
  {
    name := "updateWhenMatches: no-op when pattern doesn't match"
    run := do
      let opt : Option Int := none
      let result := updateWhenMatches (somePrism' Int) (· * 2) opt
      ensureEq "unchanged" none result
  },
  {
    name := "prismToSum: converts Some to inr"
    run := do
      let opt : Option Int := some 42
      let result := prismToSum (somePrism' Int) opt
      match result with
      | .inr n => ensureEq "right value" 42 n
      | .inl _ => throw <| IO.userError "Expected inr"
  },
  {
    name := "prismToSum: converts None to inl"
    run := do
      let opt : Option Int := none
      let result := prismToSum (somePrism' Int) opt
      match result with
      | .inl orig => ensureEq "left is original" none orig
      | .inr _ => throw <| IO.userError "Expected inl"
  }
]

/-! ## Traversal Integration Tests -/

def traversalTests : List TestCase := [
  {
    name := "mapMaybe: transforms elements selectively"
    run := do
      let nums := [1, 2, 3, 4, 5]
      -- Double only even numbers
      let result := mapMaybe traversed
        (fun n => if n % 2 == 0 then some (n * 2) else none)
        nums
      -- Odd numbers unchanged, even numbers doubled
      ensureEq "selective transform" [1, 4, 3, 8, 5] result
  },
  {
    name := "traverseOption: effectful traversal with Option"
    run := do
      let nums := [2, 4, 6]
      let result := traverseOption traversed
        (fun n => if n % 2 == 0 then some (n / 2) else none)
        nums
      ensureEq "halved evens" (some [1, 2, 3]) result
  },
  {
    name := "traverseOption: short-circuits on failure"
    run := do
      let nums := [2, 3, 6]  -- 3 is odd
      let result := traverseOption traversed
        (fun n => if n % 2 == 0 then some (n / 2) else none)
        nums
      ensureEq "failed on odd" (none : Option (List Int)) result
  }
]

/-! ## All Tests -/

def cases : List TestCase :=
  exceptTests ++ stateTests ++ readerTests ++ optionTests ++ traversalTests

end CollimatorTests.Integration
