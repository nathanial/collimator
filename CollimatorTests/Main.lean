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

  let exitCode ← runAllSuites

  IO.println ""
  if exitCode == 0 then
    IO.println "✓ All test suites passed!"
  else
    IO.println s!"✗ {exitCode} test suite(s) had failures"

  return exitCode
