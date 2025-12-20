import Crucible
import CollimatorTests.ProfunctorTests
import CollimatorTests.IsoTests
import CollimatorTests.LensTests
import CollimatorTests.PrismTests
import CollimatorTests.TraversalTests
import CollimatorTests.AffineTests
import CollimatorTests.CombinatorTests
import CollimatorTests.CompositionTests
import CollimatorTests.IntegrationTests
import CollimatorTests.DevToolsTests

/-!
# Test Runner for Collimator

Runs all test suites and reports results.
-/

open Crucible

def main : IO UInt32 := do
  IO.println "╔════════════════════════════════════════╗"
  IO.println "║     Collimator Test Suite              ║"
  IO.println "╚════════════════════════════════════════╝"

  let mut exitCode : UInt32 := 0

  exitCode := exitCode + (← runTests "Profunctor Tests" CollimatorTests.ProfunctorTests.cases)
  exitCode := exitCode + (← runTests "Iso Tests" CollimatorTests.IsoTests.cases)
  exitCode := exitCode + (← runTests "Lens Tests" CollimatorTests.LensTests.cases)
  exitCode := exitCode + (← runTests "Prism Tests" CollimatorTests.PrismTests.cases)
  exitCode := exitCode + (← runTests "Traversal Tests" CollimatorTests.TraversalTests.cases)
  exitCode := exitCode + (← runTests "Affine Tests" CollimatorTests.AffineTests.cases)
  exitCode := exitCode + (← runTests "Combinator Tests" CollimatorTests.CombinatorTests.cases)
  exitCode := exitCode + (← runTests "Composition Tests" CollimatorTests.CompositionTests.cases)
  exitCode := exitCode + (← runTests "Integration Tests" CollimatorTests.IntegrationTests.cases)
  exitCode := exitCode + (← runTests "DevTools Tests" CollimatorTests.DevTools.cases)

  IO.println ""
  if exitCode == 0 then
    IO.println "✓ All test suites passed!"
  else
    IO.println s!"✗ {exitCode} test suite(s) had failures"

  return exitCode
