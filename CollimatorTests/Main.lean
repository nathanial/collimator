import CollimatorTests.Framework
import CollimatorTests.Core
import CollimatorTests.BasicOperations
import CollimatorTests.IsoLaws
import CollimatorTests.LensLaws
import CollimatorTests.PrismLaws
import CollimatorTests.TraversalLaws
import CollimatorTests.Combinators
import CollimatorTests.Traversals
import CollimatorTests.Poly
import CollimatorTests.PhaseFiveNormalization
import CollimatorTests.PhaseFiveSubtyping
import CollimatorTests.AdvancedShowcase

/-!
# Test Runner for Collimator

Runs all test suites and reports results.
-/

open CollimatorTests

def main : IO UInt32 := do
  IO.println "╔════════════════════════════════════════╗"
  IO.println "║     Collimator Test Suite              ║"
  IO.println "╚════════════════════════════════════════╝"

  let mut exitCode : UInt32 := 0

  exitCode := exitCode + (← runTests "Core Profunctor Tests" CollimatorTests.Core.cases)
  exitCode := exitCode + (← runTests "Basic Operations" CollimatorTests.BasicOperations.cases)
  exitCode := exitCode + (← runTests "Iso Laws" CollimatorTests.IsoLaws.cases)
  exitCode := exitCode + (← runTests "Lens Laws" CollimatorTests.LensLaws.cases)
  exitCode := exitCode + (← runTests "Prism Laws" CollimatorTests.PrismLaws.cases)
  exitCode := exitCode + (← runTests "Traversal Laws" CollimatorTests.TraversalLaws.cases)
  exitCode := exitCode + (← runTests "Combinators" CollimatorTests.Combinators.cases)
  exitCode := exitCode + (← runTests "Traversals" CollimatorTests.Traversals.cases)
  exitCode := exitCode + (← runTests "Polymorphic API" CollimatorTests.Poly.cases)
  exitCode := exitCode + (← runTests "Phase Five Normalization" CollimatorTests.PhaseFiveNormalization.allTests)
  exitCode := exitCode + (← runTests "Phase Five Subtyping" CollimatorTests.PhaseFiveSubtyping.cases)

  IO.println ""
  if exitCode == 0 then
    IO.println "✓ All test suites passed!"
  else
    IO.println s!"✗ {exitCode} test suite(s) had failures"

  return exitCode
