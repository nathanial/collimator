import Collimator.Optics.Traversal
import Collimator.Concrete.FunArrow
import Collimator.Instances.List
import Collimator.Poly
import CollimatorTests.Framework
import Mathlib.Control.Monad.Writer

namespace CollimatorTests.AdvancedShowcase.EffectfulTraversals

open Collimator
open Collimator.Poly
open Collimator.Instances.List (traversed)
open CollimatorTests

/-!
# Effectful Traversals

Demonstrate traversals working with different applicative functors:
- Option applicative for validation and short-circuiting
- State applicative for stateful transformations
- Writer applicative for logging transformations
- IO applicative for effectful operations (if applicable)
- Custom applicatives for domain-specific effects

Show how the same traversal can be reused with different effect types.
-/

/-- Test: Option applicative validates all numbers are positive, short-circuits on first failure -/
private def case_optionValidatePositive : TestCase := {
  name := "Option applicative: validate all positive (short-circuit)",
  run := do
    -- Validation function: accept only positive numbers
    let validatePositive : Int → Option Int :=
      fun n => if n > 0 then some n else none

    -- Test 1: All positive - succeeds
    let allPositive : List Int := [1, 2, 3, 4, 5]
    let result1 := Traversal.traverse' traversed validatePositive allPositive
    ensureEq "All positive validates" (some [1, 2, 3, 4, 5]) result1

    -- Test 2: Contains negative - short-circuits to None
    let hasNegative : List Int := [1, 2, -3, 4, 5]
    let result2 := Traversal.traverse' traversed validatePositive hasNegative
    ensureEq "Negative causes short-circuit" (none : Option (List Int)) result2

    -- Test 3: First element negative - immediate failure
    let firstNegative : List Int := [-1, 2, 3]
    let result3 := Traversal.traverse' traversed validatePositive firstNegative
    ensureEq "First negative fails immediately" (none : Option (List Int)) result3

    -- Test 4: Empty list - succeeds trivially
    let empty : List Int := []
    let result4 := Traversal.traverse' traversed validatePositive empty
    ensureEq "Empty list validates" (some []) result4

    -- Test 5: Zero is not positive - should fail
    let hasZero : List Int := [1, 0, 3]
    let result5 := Traversal.traverse' traversed validatePositive hasZero
    ensureEq "Zero is not positive" (none : Option (List Int)) result5
}

/-- Test: Option applicative for safe division, short-circuits on divide-by-zero -/
private def case_optionSafeDivision : TestCase := {
  name := "Option applicative: safe division (short-circuit on zero)",
  run := do
    -- Safe division function: returns None if divisor is zero
    let safeDivide (divisor : Int) (dividend : Int) : Option Int :=
      if divisor = 0 then none else some (dividend / divisor)

    -- Test 1: All non-zero divisors - succeeds
    let divisors : List Int := [2, 4, 5, 10]
    let dividend := 100
    let result1 := Traversal.traverse' traversed (safeDivide · dividend) divisors
    ensureEq "All non-zero divisors succeed" (some [50, 25, 20, 10]) result1

    -- Test 2: Contains zero - short-circuits to None
    let hasZero : List Int := [2, 4, 0, 10]
    let result2 := Traversal.traverse' traversed (safeDivide · dividend) hasZero
    ensureEq "Zero divisor causes short-circuit" (none : Option (List Int)) result2

    -- Test 3: First element zero - immediate failure
    let firstZero : List Int := [0, 2, 4]
    let result3 := Traversal.traverse' traversed (safeDivide · dividend) firstZero
    ensureEq "First zero fails immediately" (none : Option (List Int)) result3

    -- Test 4: Last element zero - processes all then fails
    let lastZero : List Int := [2, 4, 5, 0]
    let result4 := Traversal.traverse' traversed (safeDivide · dividend) lastZero
    ensureEq "Last zero still fails" (none : Option (List Int)) result4

    -- Test 5: Empty list - succeeds trivially
    let empty : List Int := []
    let result5 := Traversal.traverse' traversed (safeDivide · dividend) empty
    ensureEq "Empty list succeeds" (some []) result5

    -- Test 6: Negative divisors are fine
    let negatives : List Int := [-2, -5, 10]
    let result6 := Traversal.traverse' traversed (safeDivide · dividend) negatives
    ensureEq "Negative divisors are valid" (some [-50, -20, 10]) result6
}

/-- Test: State applicative threads counter through traversal to number elements -/
private def case_stateNumberElements : TestCase := {
  name := "State applicative: number elements sequentially",
  run := do
    -- Stateful function: pair each element with current counter, then increment
    let numberElement (x : String) : StateT Nat Id (Nat × String) := do
      let n ← get
      set (n + 1)
      pure (n, x)

    -- Test 1: Number elements starting from 0
    let fruits := ["apple", "banana", "cherry"]
    let (result1, finalCount1) := (Traversal.traverse' traversed numberElement fruits).run 0
    ensureEq "Elements numbered from 0" [(0, "apple"), (1, "banana"), (2, "cherry")] result1
    ensureEq "Final counter is 3" 3 finalCount1

    -- Test 2: Number elements starting from 10
    let colors := ["red", "green", "blue"]
    let (result2, finalCount2) := (Traversal.traverse' traversed numberElement colors).run 10
    ensureEq "Elements numbered from 10" [(10, "red"), (11, "green"), (12, "blue")] result2
    ensureEq "Final counter is 13" 13 finalCount2

    -- Test 3: Empty list - counter unchanged
    let empty : List String := []
    let (result3, finalCount3) := (Traversal.traverse' traversed numberElement empty).run 5
    ensureEq "Empty list returns empty" [] result3
    ensureEq "Counter unchanged for empty list" 5 finalCount3

    -- Test 4: Single element
    let single := ["only"]
    let (result4, finalCount4) := (Traversal.traverse' traversed numberElement single).run 99
    ensureEq "Single element numbered" [(99, "only")] result4
    ensureEq "Counter incremented once" 100 finalCount4

    -- Test 5: Demonstrate state threading - use counter to create indices
    let addIndex (x : Int) : StateT Nat Id String := do
      let idx ← get
      set (idx + 1)
      pure s!"[{idx}]={x}"

    let numbers := [10, 20, 30]
    let (indexed, _) := (Traversal.traverse' traversed addIndex numbers).run 1
    ensureEq "Create indexed strings" ["[1]=10", "[2]=20", "[3]=30"] indexed
}

-- Statistics accumulator for state test
private structure Stats where
  sum : Int
  count : Nat
  max : Int
deriving Repr, BEq

-- Diagnostic types for writer test
private inductive DiagLevel
  | info
  | warning
  | error
deriving Repr, BEq, Inhabited

private structure Diagnostic where
  level : DiagLevel
  message : String
deriving Repr, BEq, Inhabited

-- Validation type for error accumulation
private inductive Validation (ε α : Type _)
  | success : α → Validation ε α
  | failure : Array ε → Validation ε α
deriving Repr, BEq

private instance {ε : Type _} : Monad (Validation ε) where
  pure a := Validation.success a
  bind v f := match v with
    | Validation.success a => f a
    | Validation.failure errs => Validation.failure errs

private instance {ε : Type _} : Functor (Validation ε) where
  map f v := match v with
    | Validation.success a => Validation.success (f a)
    | Validation.failure errs => Validation.failure errs

private instance {ε : Type _} : Applicative (Validation ε) where
  pure a := Validation.success a
  seq vf va := match vf, va () with
    | Validation.success f, Validation.success a => Validation.success (f a)
    | Validation.success _, Validation.failure errs => Validation.failure errs
    | Validation.failure errs, Validation.success _ => Validation.failure errs
    | Validation.failure errs1, Validation.failure errs2 => Validation.failure (errs1 ++ errs2)

-- Form data for validation example
private structure FormData where
  name : String
  age : Int
  email : String
deriving Repr, BEq

-- Person data for polymorphism example
private structure Person where
  name : String
  age : Int
deriving Repr, BEq

-- Additional state structures for new tests
private structure NormState where
  sum : Int
  count : Nat
deriving Repr, BEq

private structure DedupState where
  prev : Option Int
  dupCount : Nat
deriving Repr, BEq

private structure MapState where
  nextId : Nat
  mapping : List (String × Nat)  -- Simple association list
deriving Repr, BEq

private structure FreqState where
  frequencies : List (Int × Nat)  -- (value, frequency)
deriving Repr, BEq

private structure WindowState where
  window : List Int
  maxSize : Nat
deriving Repr, BEq

private structure MeanState where
  sum : Int
  count : Nat
deriving Repr, BEq

/-- Test: State applicative accumulates statistics during transformations -/
private def case_stateAccumulateStats : TestCase := {
  name := "State applicative: accumulate statistics with transformations",
  run := do
    -- Stateful function: double each number and accumulate statistics
    let doubleAndAccumulate (x : Int) : StateT Stats Id Int := do
      let stats ← get
      set ({
        sum := stats.sum + x,
        count := stats.count + 1,
        max := max stats.max x
      } : Stats)
      pure (x * 2)

    -- Test 1: Accumulate sum, count, and max while doubling
    let numbers := [5, 2, 8, 1, 9]
    let initialStats : Stats := { sum := 0, count := 0, max := 0 }
    let (doubled, finalStats) := (Traversal.traverse' traversed doubleAndAccumulate numbers).run initialStats
    ensureEq "Elements doubled" [10, 4, 16, 2, 18] doubled
    ensureEq "Sum accumulated" 25 finalStats.sum
    ensureEq "Count accumulated" 5 finalStats.count
    ensureEq "Max tracked" 9 finalStats.max

    -- Test 2: Transform with running average calculation
    let accumulateForAvg (x : Int) : StateT (Int × Nat) Id Int := do
      let (sum, count) ← get
      let newSum := sum + x
      let newCount := count + 1
      set (newSum, newCount)
      pure (x + 10)  -- Transform: add 10 to each element

    let values := [15, 25, 35]
    let (transformed, (totalSum, totalCount)) := (Traversal.traverse' traversed accumulateForAvg values).run (0, 0)
    ensureEq "Values transformed (+10)" [25, 35, 45] transformed
    ensureEq "Total sum for average" 75 totalSum
    ensureEq "Total count" 3 totalCount
    -- Average would be: totalSum / totalCount = 75 / 3 = 25

    -- Test 3: Empty list - stats unchanged
    let empty : List Int := []
    let (emptyResult, emptyStats) := (Traversal.traverse' traversed doubleAndAccumulate empty).run initialStats
    ensureEq "Empty list unchanged" [] emptyResult
    ensureEq "Stats remain initial" initialStats emptyStats

    -- Test 4: Single element accumulation
    let single := [42]
    let (singleResult, singleStats) := (Traversal.traverse' traversed doubleAndAccumulate single).run initialStats
    ensureEq "Single element doubled" [84] singleResult
    ensureEq "Single sum" 42 singleStats.sum
    ensureEq "Single count" 1 singleStats.count
    ensureEq "Single max" 42 singleStats.max
}

/-- Test: Writer applicative logs each transformation step -/
private def case_writerLogTransformations : TestCase := {
  name := "Writer applicative: log each transformation step",
  run := do
    -- Transformation function that logs before/after for each element
    let transformAndLog (x : Int) : WriterT (Array String) Id Int := do
      let result := x * 2 + 1
      tell #[s!"Transform {x} -> {result}"]
      pure result

    -- Test 1: Log all transformations
    let numbers := [3, 5, 7]
    let (transformed, log) := (Traversal.traverse' traversed transformAndLog numbers).run
    ensureEq "All elements transformed" [7, 11, 15] transformed
    ensureEq "All transformations logged"
      #["Transform 3 -> 7", "Transform 5 -> 11", "Transform 7 -> 15"]
      log

    -- Test 2: Empty list produces empty log
    let empty : List Int := []
    let (emptyResult, emptyLog) := (Traversal.traverse' traversed transformAndLog empty).run
    ensureEq "Empty result" [] emptyResult
    ensureEq "Empty log" #[] emptyLog

    -- Test 3: Single element
    let single := [10]
    let (singleResult, singleLog) := (Traversal.traverse' traversed transformAndLog single).run
    ensureEq "Single transformation" [21] singleResult
    ensureEq "Single log entry" #["Transform 10 -> 21"] singleLog

    -- Test 4: Log validation messages during transformation
    let validateAndTransform (x : Int) : WriterT (Array String) Id Int := do
      if x < 0 then
        tell #[s!"Warning: negative value {x}"]
      else if x = 0 then
        tell #[s!"Warning: zero value"]
      else
        tell #[s!"OK: {x}"]
      pure (x.natAbs)

    let mixed := [-5, 0, 10, -2]
    let (validated, validationLog) := (Traversal.traverse' traversed validateAndTransform mixed).run
    ensureEq "Validated values" [5, 0, 10, 2] validated
    ensureEq "Validation log collected"
      #["Warning: negative value -5", "Warning: zero value", "OK: 10", "Warning: negative value -2"]
      validationLog

    -- Test 5: Accumulate computations with details
    let computeWithDetail (x : Int) : WriterT (Array String) Id Int := do
      let squared := x * x
      let doubled := squared * 2
      tell #[s!"{x}² = {squared}, then *2 = {doubled}"]
      pure doubled

    let inputs := [2, 3]
    let (computed, computeLog) := (Traversal.traverse' traversed computeWithDetail inputs).run
    ensureEq "Computed results" [8, 18] computed
    ensureEq "Computation steps logged"
      #["2² = 4, then *2 = 8", "3² = 9, then *2 = 18"]
      computeLog
}

/-- Test: Writer applicative collects diagnostics with severity levels -/
private def case_writerCollectDiagnostics : TestCase := {
  name := "Writer applicative: collect diagnostics during traversal",
  run := do
    -- Transformation with diagnostic collection
    let processWithDiagnostics (x : Int) : WriterT (Array Diagnostic) Id Int := do
      if x < 0 then
        tell #[{ level := DiagLevel.error, message := s!"Negative value: {x}" }]
        pure 0
      else if x = 0 then
        tell #[{ level := DiagLevel.warning, message := "Zero value encountered" }]
        pure 0
      else if x > 100 then
        tell #[{ level := DiagLevel.warning, message := s!"Large value: {x}" }]
        pure x
      else
        tell #[{ level := DiagLevel.info, message := s!"Processing: {x}" }]
        pure x

    -- Test 1: Collect mixed diagnostics
    let values := [50, -10, 0, 150, 25]
    let (results, diagnostics) := (Traversal.traverse' traversed processWithDiagnostics values).run
    ensureEq "Values processed" [50, 0, 0, 150, 25] results
    ensureEq "Diagnostics count" 5 diagnostics.size
    ensureEq "First diagnostic is info"
      { level := DiagLevel.info, message := "Processing: 50" }
      diagnostics[0]!
    ensureEq "Second diagnostic is error"
      { level := DiagLevel.error, message := "Negative value: -10" }
      diagnostics[1]!
    ensureEq "Third diagnostic is warning"
      { level := DiagLevel.warning, message := "Zero value encountered" }
      diagnostics[2]!

    -- Test 2: Multiple diagnostics per element
    let processWithMultipleDiagnostics (x : Int) : WriterT (Array Diagnostic) Id Int := do
      tell #[{ level := DiagLevel.info, message := s!"Starting process: {x}" }]
      let result := x * 2
      if result > 50 then
        tell #[{ level := DiagLevel.warning, message := s!"Result {result} exceeds threshold" }]
      tell #[{ level := DiagLevel.info, message := s!"Completed: {x} -> {result}" }]
      pure result

    let inputs := [10, 30]
    let (doubled, logs) := (Traversal.traverse' traversed processWithMultipleDiagnostics inputs).run
    ensureEq "Results doubled" [20, 60] doubled
    ensureEq "Multiple logs per element" 5 logs.size
    -- 10: start, complete (2)
    -- 30: start, warning, complete (3)

    -- Test 3: Filter diagnostics by level (post-processing)
    let countByLevel (diags : Array Diagnostic) (level : DiagLevel) : Nat :=
      diags.foldl (fun acc d => if d.level == level then acc + 1 else acc) 0

    let testValues := [5, -1, 200, 0, 10]
    let (_, allDiags) := (Traversal.traverse' traversed processWithDiagnostics testValues).run
    let errorCount := countByLevel allDiags DiagLevel.error
    let warningCount := countByLevel allDiags DiagLevel.warning
    let infoCount := countByLevel allDiags DiagLevel.info
    ensureEq "Error count" 1 errorCount
    ensureEq "Warning count" 2 warningCount
    ensureEq "Info count" 2 infoCount

    -- Test 4: Empty list produces no diagnostics
    let empty : List Int := []
    let (emptyResults, emptyDiags) := (Traversal.traverse' traversed processWithDiagnostics empty).run
    ensureEq "Empty results" [] emptyResults
    ensureEq "No diagnostics" 0 emptyDiags.size
}

/-- Test: Validation applicative accumulates all errors, unlike Option -/
private def case_validationAccumulateErrors : TestCase := {
  name := "Validation applicative: accumulate all errors (vs Option short-circuit)",
  run := do
    -- Validation function that returns error for invalid values
    let validatePositive (x : Int) : Validation String Int :=
      if x > 0 then
        Validation.success x
      else
        Validation.failure #[s!"Value {x} is not positive"]

    -- Test 1: All valid - succeeds
    let allValid := [1, 2, 3, 4]
    let result1 := Traversal.traverse' traversed validatePositive allValid
    match result1 with
    | Validation.success vals =>
      ensureEq "All valid values pass" [1, 2, 3, 4] vals
    | Validation.failure _ =>
      IO.throwServerError "Expected success but got failure"

    -- Test 2: Multiple failures - ACCUMULATES ALL (not short-circuit like Option)
    let multipleInvalid := [1, -2, 3, -4, 0]
    let result2 := Traversal.traverse' traversed validatePositive multipleInvalid
    match result2 with
    | Validation.success _ =>
      IO.throwServerError "Expected failure but got success"
    | Validation.failure errs =>
      ensureEq "All three errors accumulated" 3 errs.size
      ensureEq "First error" "Value -2 is not positive" errs[0]!
      ensureEq "Second error" "Value -4 is not positive" errs[1]!
      ensureEq "Third error" "Value 0 is not positive" errs[2]!

    -- Test 3: Compare with Option (short-circuits on first error)
    let optionValidate (x : Int) : Option Int :=
      if x > 0 then some x else none

    let result3Option := Traversal.traverse' traversed optionValidate multipleInvalid
    match result3Option with
    | none => pure ()  -- Option just returns None, doesn't tell us which/how many failed
    | some _ => IO.throwServerError "Expected None"

    -- Key insight: Validation gives us ALL errors, Option gives us nothing
    let result3Validation := Traversal.traverse' traversed validatePositive multipleInvalid
    match result3Validation with
    | Validation.failure errs =>
      ensureEq "Validation tells us exactly what failed" 3 errs.size
    | Validation.success _ =>
      IO.throwServerError "Expected failure"

    -- Test 4: Form validation use case - validate multiple fields
    let validateField (field : String) (condition : Bool) : Validation String Unit :=
      if condition then
        Validation.success ()
      else
        Validation.failure #[s!"{field} is invalid"]

    let validateForm (form : FormData) : Validation String FormData :=
      -- Validate all fields and accumulate errors
      let nameValid := validateField "name" (!form.name.isEmpty)
      let ageValid := validateField "age" (form.age >= 0 && form.age <= 150)
      let emailValid := validateField "email" (form.email.contains '@')

      match nameValid, ageValid, emailValid with
      | Validation.success _, Validation.success _, Validation.success _ =>
        Validation.success form
      | _, _, _ =>
        let errors := #[]
        let errors := match nameValid with
          | Validation.failure e => errors ++ e
          | _ => errors
        let errors := match ageValid with
          | Validation.failure e => errors ++ e
          | _ => errors
        let errors := match emailValid with
          | Validation.failure e => errors ++ e
          | _ => errors
        Validation.failure errors

    let badForm : FormData := { name := "", age := -5, email := "notanemail" }
    match validateForm badForm with
    | Validation.failure errs =>
      ensureEq "All three field errors reported" 3 errs.size
    | Validation.success _ =>
      IO.throwServerError "Expected validation failure"

    -- Test 5: Empty list succeeds trivially
    let empty : List Int := []
    let result5 := Traversal.traverse' traversed validatePositive empty
    match result5 with
    | Validation.success vals =>
      ensureEq "Empty list succeeds" [] vals
    | Validation.failure _ =>
      IO.throwServerError "Empty list should succeed"
}

/-- Test: State applicative replaces elements with running sum -/
private def case_stateRunningSum : TestCase := {
  name := "State applicative: replace elements with running sum",
  run := do
    -- Stateful function: replace each element with current sum, then add element to sum
    let replaceWithSum (x : Int) : StateT Int Id Int := do
      let currentSum ← get
      set (currentSum + x)
      pure currentSum  -- Return sum BEFORE adding current element

    -- Test 1: Running sum starting from 0
    let numbers := [5, 10, 15, 20]
    let (result1, finalSum1) := (Traversal.traverse' traversed replaceWithSum numbers).run 0
    ensureEq "Elements replaced with running sum" [0, 5, 15, 30] result1
    ensureEq "Final sum" 50 finalSum1

    -- Test 2: Running sum starting from 100
    let (result2, finalSum2) := (Traversal.traverse' traversed replaceWithSum numbers).run 100
    ensureEq "Elements replaced with running sum from 100" [100, 105, 115, 130] result2
    ensureEq "Final sum from 100" 150 finalSum2

    -- Test 3: Empty list - sum unchanged
    let empty : List Int := []
    let (result3, finalSum3) := (Traversal.traverse' traversed replaceWithSum empty).run 42
    ensureEq "Empty list" [] result3
    ensureEq "Sum unchanged" 42 finalSum3

    -- Test 4: Negative numbers
    let mixed := [10, -5, 20, -15]
    let (result4, finalSum4) := (Traversal.traverse' traversed replaceWithSum mixed).run 0
    ensureEq "Mixed positive/negative" [0, 10, 5, 25] result4
    ensureEq "Final sum with negatives" 10 finalSum4

    -- Test 5: Replace with running product
    let replaceWithProduct (x : Int) : StateT Int Id Int := do
      let currentProduct ← get
      set (currentProduct * x)
      pure currentProduct

    let factors := [2, 3, 4]
    let (products, finalProduct) := (Traversal.traverse' traversed replaceWithProduct factors).run 1
    ensureEq "Running products" [1, 2, 6] products
    ensureEq "Final product" 24 finalProduct
}

/-- Test: State applicative normalizes values based on running statistics -/
private def case_stateNormalizeByStats : TestCase := {
  name := "State applicative: normalize values by running mean",
  run := do
    -- Normalize by running mean: transform each value, then update statistics
    let normalizeByMean (x : Int) : StateT NormState Id Int := do
      let state ← get
      let currentMean := if state.count > 0 then state.sum / state.count else 0
      set ({ sum := state.sum + x, count := state.count + 1 } : NormState)
      pure (x - currentMean)  -- Subtract current mean from value

    -- Test 1: Normalize sequence
    let values := [10, 20, 30, 40]
    let initialState : NormState := { sum := 0, count := 0 }
    let (normalized, finalState) := (Traversal.traverse' traversed normalizeByMean values).run initialState
    ensureEq "Normalized by running mean" [10, 10, 15, 20] normalized
    -- [10-0, 20-10, 30-15, 40-20]
    ensureEq "Final sum" 100 finalState.sum
    ensureEq "Final count" 4 finalState.count

    -- Test 2: Scale by running max
    let scaleByMax (x : Int) : StateT Int Id Int := do
      let currentMax ← get
      let newMax := max currentMax x
      set newMax
      if currentMax > 0 then
        pure (x * 100 / currentMax)  -- Scale as percentage of current max
      else
        pure 100  -- First element is 100%

    let sequence := [50, 100, 75, 200]
    let (scaled, _) := (Traversal.traverse' traversed scaleByMax sequence).run 0
    ensureEq "Scaled by running max" [100, 200, 75, 200] scaled
    -- [100% (first), 100*100/50=200%, 75*100/100=75%, 200*100/100=200%]
}

/-- Test: State applicative deduplicates consecutive elements -/
private def case_stateDeduplicateConsecutive : TestCase := {
  name := "State applicative: mark duplicates of previous element",
  run := do
    -- State tracks the previous element
    -- Replace duplicates with a marker value
    let dedup (marker : Int) (x : Int) : StateT (Option Int) Id Int := do
      let prev ← get
      set (some x)
      match prev with
      | none => pure x  -- First element, keep it
      | some p => if p == x then pure marker else pure x

    -- Test 1: Deduplicate consecutive duplicates
    let withDups := [1, 1, 2, 2, 2, 3, 1, 1]
    let (result1, _) := (Traversal.traverse' traversed (dedup (-1)) withDups).run none
    ensureEq "Consecutive duplicates marked as -1" [1, -1, 2, -1, -1, 3, 1, -1] result1

    -- Test 2: No duplicates
    let noDups := [1, 2, 3, 4, 5]
    let (result2, _) := (Traversal.traverse' traversed (dedup (-1)) noDups).run none
    ensureEq "No duplicates, all kept" [1, 2, 3, 4, 5] result2

    -- Test 3: All same
    let allSame := [7, 7, 7, 7]
    let (result3, _) := (Traversal.traverse' traversed (dedup 0) allSame).run none
    ensureEq "All same except first" [7, 0, 0, 0] result3

    -- Test 4: Empty list
    let empty : List Int := []
    let (result4, _) := (Traversal.traverse' traversed (dedup (-1)) empty).run none
    ensureEq "Empty list" [] result4

    -- Test 5: Count consecutive duplicates
    let countDuplicates (x : Int) : StateT DedupState Id Int := do
      let state ← get
      match state.prev with
      | none =>
        set ({ prev := some x, dupCount := 0 } : DedupState)
        pure x
      | some p =>
        if p == x then
          set ({ prev := some x, dupCount := state.dupCount + 1 } : DedupState)
          pure x
        else
          set ({ prev := some x, dupCount := state.dupCount } : DedupState)
          pure x

    let testSeq := [5, 5, 5, 3, 3, 1]
    let (_, finalState) := (Traversal.traverse' traversed countDuplicates testSeq).run
      { prev := none, dupCount := 0 }
    ensureEq "Counted 3 duplicate occurrences" 3 finalState.dupCount
}

/-- Test: State applicative implements stateful replacements via lookup table -/
private def case_stateReplacementMap : TestCase := {
  name := "State applicative: build replacement map during traversal",
  run := do
    -- Build a replacement map as we traverse: first occurrence gets ID, repeats use that ID
    let assignId (s : String) : StateT MapState Id Nat := do
      let state ← get
      -- Look up if we've seen this string before
      match state.mapping.find? (fun pair => pair.1 == s) with
      | some pair => pure pair.2  -- Return existing ID
      | none =>
        let newId := state.nextId
        set ({
          nextId := state.nextId + 1,
          mapping := (s, newId) :: state.mapping
        } : MapState)
        pure newId

    -- Test 1: Assign unique IDs to strings, reuse for duplicates
    let words := ["apple", "banana", "apple", "cherry", "banana", "apple"]
    let initialState : MapState := { nextId := 0, mapping := [] }
    let (ids, finalState) := (Traversal.traverse' traversed assignId words).run initialState
    ensureEq "Unique IDs assigned and reused" [0, 1, 0, 2, 1, 0] ids
    ensureEq "Three unique strings" 3 finalState.nextId
    ensureEq "Mapping contains 3 entries" 3 finalState.mapping.length

    -- Test 2: Empty list
    let empty : List String := []
    let (emptyIds, emptyState) := (Traversal.traverse' traversed assignId empty).run initialState
    ensureEq "Empty result" [] emptyIds
    ensureEq "No IDs assigned" 0 emptyState.nextId

    -- Test 3: All unique
    let unique := ["a", "b", "c", "d"]
    let (uniqueIds, uniqueState) := (Traversal.traverse' traversed assignId unique).run initialState
    ensureEq "All unique IDs" [0, 1, 2, 3] uniqueIds
    ensureEq "Four IDs assigned" 4 uniqueState.nextId

    -- Test 4: Replace based on accumulated frequency
    let replaceByFrequency (x : Int) : StateT FreqState Id Nat := do
      let state ← get
      match state.frequencies.find? (fun pair => pair.1 == x) with
      | some pair =>
        -- Update frequency
        let freq := pair.2
        let newFreqs := state.frequencies.map fun (v, f) =>
          if v == x then (v, f + 1) else (v, f)
        set ({ frequencies := newFreqs } : FreqState)
        pure (freq + 1)  -- Return new frequency
      | none =>
        set ({ frequencies := (x, 1) :: state.frequencies } : FreqState)
        pure 1  -- First occurrence

    let numbers := [5, 3, 5, 5, 3, 7, 5]
    let (freqs, _) := (Traversal.traverse' traversed replaceByFrequency numbers).run
      { frequencies := [] }
    ensureEq "Replace with occurrence count" [1, 1, 2, 3, 2, 1, 4] freqs
    -- 5 appears: 1st, 2nd, 3rd, 4th time
    -- 3 appears: 1st, 2nd time
    -- 7 appears: 1st time
}

/-- Test: State applicative implements sliding window transformations -/
private def case_stateSlidingWindow : TestCase := {
  name := "State applicative: sliding window transformations",
  run := do
    -- Replace each element with average of current window
    let windowAverage (x : Int) : StateT WindowState Id Int := do
      let state ← get
      let newWindow := (x :: state.window).take state.maxSize
      set ({ window := newWindow, maxSize := state.maxSize } : WindowState)
      let sum := newWindow.foldl (· + ·) 0
      let count := newWindow.length
      pure (if count > 0 then sum / count else 0)

    -- Test 1: Window size 2 - average of current and previous
    let numbers := [10, 20, 30, 40, 50]
    let initialState : WindowState := { window := [], maxSize := 2 }
    let (averages, _) := (Traversal.traverse' traversed windowAverage numbers).run initialState
    ensureEq "Window averages (size 2)" [10, 15, 25, 35, 45] averages
    -- [10/1, (20+10)/2, (30+20)/2, (40+30)/2, (50+40)/2]

    -- Test 2: Window size 3
    let (averages3, _) := (Traversal.traverse' traversed windowAverage numbers).run
      { window := [], maxSize := 3 }
    ensureEq "Window averages (size 3)" [10, 15, 20, 30, 40] averages3
    -- [10/1, (20+10)/2, (30+20+10)/3, (40+30+20)/3, (50+40+30)/3]

    -- Test 3: Window size 1 (no averaging)
    let (averages1, _) := (Traversal.traverse' traversed windowAverage numbers).run
      { window := [], maxSize := 1 }
    ensureEq "Window size 1 returns element itself" [10, 20, 30, 40, 50] averages1

    -- Test 4: Compute differences from previous element
    let computeDelta (x : Int) : StateT (Option Int) Id Int := do
      let prev ← get
      set (some x)
      match prev with
      | none => pure 0  -- First element: no previous
      | some p => pure (x - p)

    let sequence := [5, 8, 6, 9, 12]
    let (deltas, _) := (Traversal.traverse' traversed computeDelta sequence).run none
    ensureEq "Deltas from previous" [0, 3, -2, 3, 3] deltas

    -- Test 5: Running differences (element minus running mean)
    let deltaFromMean (x : Int) : StateT MeanState Id Int := do
      let state ← get
      let mean := if state.count > 0 then state.sum / state.count else x
      set ({ sum := state.sum + x, count := state.count + 1 } : MeanState)
      pure (x - mean)

    let values := [100, 200, 150, 250]
    let (diffs, _) := (Traversal.traverse' traversed deltaFromMean values).run
      { sum := 0, count := 0 }
    ensureEq "Differences from running mean" [0, 100, 0, 100] diffs
    -- [100-100, 200-100, 150-150, 250-150]
}

/-- Test: Polymorphism - same traversal works with any Applicative -/
private def case_polymorphicTraversal : TestCase := {
  name := "Polymorphism: same traversal, multiple effect types",
  run := do
    -- Define a single list to traverse
    let numbers : List Int := [5, 10, 15, 20]

    -- Define a processing function that can be used with ANY applicative
    -- The type signature is polymorphic over the effect type F
    let processNumber (threshold : Int) (x : Int) {F : Type → Type} [Applicative F]
        (successFn : Int → F Int) (failFn : String → F Int) : F Int :=
      if x >= threshold then
        successFn x
      else
        failFn s!"Value {x} below threshold {threshold}"

    -- Use case 1: Option - fail-fast validation
    let optionProcess := processNumber 5  -- threshold of 5, all values pass
    let optionResult := Traversal.traverse' traversed
      (fun x => optionProcess x (fun v => some v) (fun _ => none))
      numbers
    match optionResult with
    | some vals =>
      ensureEq "Option: all values >= 5 pass" [5, 10, 15, 20] vals
    | none =>
      IO.throwServerError "Should not fail"

    let failNumbers := [5, 3, 15]
    let optionResult2 := Traversal.traverse' traversed
      (fun x => optionProcess x (fun v => some v) (fun _ => none))
      failNumbers
    match optionResult2 with
    | none =>
      pure ()  -- Expected: fails fast on first value < 10
    | some _ =>
      IO.throwServerError "Should fail"

    -- Use case 2: State - count how many values meet threshold
    let stateFn (x : Int) : StateT Nat Id Int :=
      if x >= 10 then do
        modify (· + 1)
        pure x
      else
        pure x
    let (stateVals, count) := (Traversal.traverse' traversed stateFn numbers).run 0
    ensureEq "State: values unchanged" [5, 10, 15, 20] stateVals
    ensureEq "State: counted values >= 10" 3 count

    -- Use case 3: Writer - log which values are processed
    let writerFn (x : Int) : WriterT (Array String) Id Int := do
      if x >= 10 then
        tell #[s!"Accepted: {x}"]
      else
        tell #[s!"Below threshold: {x}"]
      pure x
    let (writerVals, log) := (Traversal.traverse' traversed writerFn numbers).run
    ensureEq "Writer: values unchanged" [5, 10, 15, 20] writerVals
    ensureEq "Writer: logged all operations" 4 log.size
    ensureEq "Writer: first log entry" "Below threshold: 5" log[0]!
    ensureEq "Writer: second log entry" "Accepted: 10" log[1]!

    -- Use case 4: Validation - collect ALL failures (not fail-fast)
    let validationFn (x : Int) : Validation String Int :=
      if x >= 10 then
        Validation.success x
      else
        Validation.failure #[s!"Value {x} is below threshold 10"]
    let validationResult := Traversal.traverse' traversed validationFn failNumbers
    match validationResult with
    | Validation.failure errs =>
      ensureEq "Validation: collected both errors" 2 errs.size
      ensureEq "Validation: first error" "Value 5 is below threshold 10" errs[0]!
      ensureEq "Validation: second error" "Value 3 is below threshold 10" errs[1]!
    | Validation.success _ =>
      IO.throwServerError "Should accumulate errors"

    -- Key insight demonstration: The traversal is the SAME (`Traversal.traverse' traversed`)
    -- Only the effectful function changes!
    -- - Option: fail-fast, returns Some or None
    -- - State: thread state through traversal
    -- - Writer: collect logs during traversal
    -- - Validation: accumulate all errors

    -- Use case 5: Demonstrate with a more complex traversal
    let people : List Person := [
      { name := "Alice", age := 25 },
      { name := "Bob", age := 17 },
      { name := "Charlie", age := 30 }
    ]

    -- Same traversal, different effects!

    -- With Option: validate all are adults
    let optionValidate (p : Person) : Option Person :=
      if p.age >= 18 then some p else none
    let optionPeople := Traversal.traverse' traversed optionValidate people
    match optionPeople with
    | none => pure ()  -- Bob is 17, fails
    | some _ => IO.throwServerError "Should fail on Bob"

    -- With Writer: log age checks
    let writerValidate (p : Person) : WriterT (Array String) Id Person := do
      if p.age >= 18 then
        tell #[s!"{p.name} (age {p.age}): adult"]
      else
        tell #[s!"{p.name} (age {p.age}): minor"]
      pure p
    let (_, peopleLog) := (Traversal.traverse' traversed writerValidate people).run
    ensureEq "People log count" 3 peopleLog.size
    ensureEq "Alice logged as adult" "Alice (age 25): adult" peopleLog[0]!
    ensureEq "Bob logged as minor" "Bob (age 17): minor" peopleLog[1]!

    -- With Validation: collect all minors
    let validationValidate (p : Person) : Validation String Person :=
      if p.age >= 18 then
        Validation.success p
      else
        Validation.failure #[s!"{p.name} is {p.age} years old (under 18)"]
    let validationPeople := Traversal.traverse' traversed validationValidate people
    match validationPeople with
    | Validation.failure errs =>
      ensureEq "Found one minor" 1 errs.size
      ensureEq "Bob is minor" "Bob is 17 years old (under 18)" errs[0]!
    | Validation.success _ =>
      IO.throwServerError "Should report minor"
}

def cases : List TestCase := [
  case_optionValidatePositive,
  case_optionSafeDivision,
  case_stateNumberElements,
  case_stateAccumulateStats,
  case_stateRunningSum,
  case_stateNormalizeByStats,
  case_stateDeduplicateConsecutive,
  case_stateReplacementMap,
  case_stateSlidingWindow,
  case_writerLogTransformations,
  case_writerCollectDiagnostics,
  case_validationAccumulateErrors,
  case_polymorphicTraversal
]

end CollimatorTests.AdvancedShowcase.EffectfulTraversals
