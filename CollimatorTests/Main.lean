import CollimatorTests.Framework
import CollimatorTests.Core
import CollimatorTests.BasicOperations
import CollimatorTests.IsoLaws
import CollimatorTests.LensLaws
import CollimatorTests.PrismLaws
import CollimatorTests.TraversalLaws
import CollimatorTests.AffineLaws
import CollimatorTests.Combinators
import CollimatorTests.Traversals
import CollimatorTests.Poly
import CollimatorTests.PhaseFiveNormalization
import CollimatorTests.PhaseFiveSubtyping
import CollimatorTests.AdvancedShowcase
import CollimatorTests.GetterReview
import CollimatorTests.PropertyTests
import CollimatorTests.ConcreteProfunctors
import CollimatorTests.EdgeCases

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
  exitCode := exitCode + (← runTests "Affine Laws" CollimatorTests.AffineLaws.cases)
  exitCode := exitCode + (← runTests "Combinators" CollimatorTests.Combinators.cases)
  exitCode := exitCode + (← runTests "Traversals" CollimatorTests.Traversals.cases)
  exitCode := exitCode + (← runTests "Polymorphic API" CollimatorTests.Poly.cases)
  exitCode := exitCode + (← runTests "Phase Five Normalization" CollimatorTests.PhaseFiveNormalization.allTests)
  exitCode := exitCode + (← runTests "Phase Five Subtyping" CollimatorTests.PhaseFiveSubtyping.cases)
  exitCode := exitCode + (← runTests "Getter and Review" CollimatorTests.GetterReview.cases)

  -- Advanced Showcase tests
  exitCode := exitCode + (← runTests "Deep Composition" CollimatorTests.AdvancedShowcase.DeepComposition.cases)
  exitCode := exitCode + (← runTests "Effectful Traversals" CollimatorTests.AdvancedShowcase.EffectfulTraversals.cases)
  exitCode := exitCode + (← runTests "Filtered Indexed" CollimatorTests.AdvancedShowcase.FilteredIndexed.cases)
  exitCode := exitCode + (← runTests "Heterogeneous Compositions" CollimatorTests.AdvancedShowcase.HeterogeneousCompositions.cases)
  exitCode := exitCode + (← runTests "Polymorphic Isos" CollimatorTests.AdvancedShowcase.PolymorphicIsos.cases)
  exitCode := exitCode + (← runTests "Affine Wizardry" CollimatorTests.AdvancedShowcase.AffineWizardry.cases)
  exitCode := exitCode + (← runTests "Prism Magic" CollimatorTests.AdvancedShowcase.PrismMagic.cases)
  exitCode := exitCode + (← runTests "Mind Bending" CollimatorTests.AdvancedShowcase.MindBending.cases)

  -- New test suites
  exitCode := exitCode + (← runTests "Property Tests" CollimatorTests.PropertyTests.cases)
  exitCode := exitCode + (← runTests "Concrete Profunctors" CollimatorTests.ConcreteProfunctors.cases)
  exitCode := exitCode + (← runTests "Edge Cases" CollimatorTests.EdgeCases.cases)

  IO.println ""
  if exitCode == 0 then
    IO.println "✓ All test suites passed!"
  else
    IO.println s!"✗ {exitCode} test suite(s) had failures"

  return exitCode
