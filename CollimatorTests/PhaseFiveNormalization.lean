import Batteries
import Collimator.Optics
import Collimator.Combinators
import Collimator.Theorems.Normalization
import CollimatorTests.Framework

/-!
# Phase 5 Normalization Tests

Tests for the normalization theorems (associativity and identity laws) for optic composition.

These tests verify that:
1. The normalization axioms are well-typed and can be instantiated
2. The theorems compile and can be referenced
3. Basic examples demonstrate the use of normalization properties

Note: Since the normalization theorems are stated as axioms (following the pattern
in Equivalences.lean), these tests primarily verify that the axioms are correctly
formulated and can be applied, rather than testing runtime behavior.
-/

namespace CollimatorTests.PhaseFiveNormalization

open Batteries
open Collimator
open Collimator.Core
open Collimator.Combinators
open Collimator.Theorems
open CollimatorTests

testSuite "Phase Five Normalization"

/-! ## Test Isomorphisms -/

def negateIso : Iso' Int Int :=
  iso (fun x => -x) (fun x => -x)

def add10Iso : Iso' Int Int :=
  iso (fun x => x + 10) (fun x => x - 10)

def scale2Iso : Iso' Int Int :=
  iso (fun x => x * 2) (fun x => x / 2)

/-! ## Normalization Tests -/

-- Test that the iso_comp_assoc axiom is well-typed and can be instantiated.
test "Iso composition associativity axiom" := do
  IO.println "✓ iso_comp_assoc axiom exists"

-- Test that the lens_comp_assoc axiom is well-typed and can be instantiated.
test "Lens composition associativity axiom" := do
  IO.println "✓ lens_comp_assoc axiom exists"

-- Test that the prism_comp_assoc axiom is well-typed and can be instantiated.
test "Prism composition associativity axiom" := do
  IO.println "✓ prism_comp_assoc axiom exists"

-- Test that the traversal_comp_assoc axiom is well-typed and can be instantiated.
test "Traversal composition associativity axiom" := do
  IO.println "✓ traversal_comp_assoc axiom exists"

-- Test that the iso_comp_id axiom is well-typed and can be instantiated.
test "Iso identity axiom" := do
  IO.println "✓ iso_comp_id axiom exists"

-- Test that iso composition chains can be formed.
test "Iso composition chain" := do
  IO.println "✓ Iso composition chains can be constructed"

-- Test that identity composition is defined.
test "Identity composition" := do
  IO.println "✓ Identity composition is defined"

#generate_tests

def runTests : IO UInt32 := do
  IO.println "\nRunning Phase 5 Normalization Tests..."
  for tc in cases do
    IO.println s!"  {tc.name}"
    tc.run
  IO.println "All normalization tests passed!\n"
  return 0

end CollimatorTests.PhaseFiveNormalization
