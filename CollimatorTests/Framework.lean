/-!
# Test Framework for Collimator

Simple test harness providing TestCase structure and assertion functions.
-/

namespace CollimatorTests

/-- A test case with a name and a monadic test action. -/
structure TestCase where
  name : String
  run : IO Unit

/-- Assert that a condition is true. -/
def ensure (cond : Bool) (msg : String) : IO Unit := do
  if !cond then
    throw <| IO.userError s!"Assertion failed: {msg}"

/-- Assert that two values are equal. -/
def ensureEq [BEq α] [Repr α] (msg : String) (expected : α) (actual : α) : IO Unit := do
  if expected != actual then
    throw <| IO.userError s!"Assertion failed: {msg}\n  expected: {repr expected}\n  actual:   {repr actual}"

/-- Run a single test case. -/
def runTest (tc : TestCase) : IO Bool := do
  IO.print s!"  {tc.name}... "
  try
    tc.run
    IO.println "✓"
    return true
  catch e =>
    IO.println s!"✗\n    {e}"
    return false

/-- Run a list of test cases and report results. -/
def runTests (name : String) (cases : List TestCase) : IO UInt32 := do
  IO.println s!"\n{name}"
  IO.println ("─".intercalate (List.replicate name.length ""))
  let mut passed := 0
  let mut failed := 0
  for tc in cases do
    if ← runTest tc then
      passed := passed + 1
    else
      failed := failed + 1
  IO.println s!"\nResults: {passed} passed, {failed} failed"
  return if failed > 0 then 1 else 0

end CollimatorTests
