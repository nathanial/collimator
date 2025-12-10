import CollimatorTests.Framework
import Collimator.Prelude
import Collimator.Testing
import Collimator.Tracing
import Collimator.Commands

/-!
# Tests for Tooling Utilities

Tests for property-based testing integration and composition tracing.
-/

open Collimator
open Collimator.Testing
open Collimator.Tracing
open Collimator.Instances.Option
open CollimatorTests

namespace CollimatorTests.Tooling

/-! ## Test Structures -/

private structure TestPair where
  fst : Int
  snd : Int
deriving BEq, Repr

private def fstLens : Lens' TestPair Int :=
  lens' (·.fst) (fun p v => { p with fst := v })

private def sndLens : Lens' TestPair Int :=
  lens' (·.snd) (fun p v => { p with snd := v })

/-- Generator for TestPair -/
private def genTestPair : RandState → TestPair × RandState :=
  fun r =>
    let (f, r1) := r.nextInt (-100) 100
    let (s, r2) := r1.nextInt (-100) 100
    (⟨f, s⟩, r2)

/-! ## Property Testing Tests -/

def propertyTests : List TestCase := [
  {
    name := "testGetPut: returns true for lawful lens"
    run := do
      let pair := TestPair.mk 10 20
      ensure (testGetPut fstLens pair 99) "GetPut should hold"
  },
  {
    name := "testPutGet: returns true for lawful lens"
    run := do
      let pair := TestPair.mk 10 20
      ensure (testPutGet fstLens pair) "PutGet should hold"
  },
  {
    name := "testPutPut: returns true for lawful lens"
    run := do
      let pair := TestPair.mk 10 20
      ensure (testPutPut fstLens pair 5 99) "PutPut should hold"
  },
  {
    name := "testPreviewReview: returns true for somePrism"
    run := do
      ensure (testPreviewReview (somePrism' Int) 42) "PreviewReview should hold"
  },
  {
    name := "testReviewPreview: returns true for matching Some"
    run := do
      let opt : Option Int := some 42
      ensure (testReviewPreview (somePrism' Int) opt) "ReviewPreview should hold for Some"
  },
  {
    name := "testReviewPreview: returns true for None (vacuously)"
    run := do
      let opt : Option Int := none
      ensure (testReviewPreview (somePrism' Int) opt) "ReviewPreview vacuously true for None"
  },
  {
    name := "testBackForward: returns true for swap iso"
    run := do
      let swapIso : Iso' (Int × Int) (Int × Int) :=
        iso (forward := fun (a, b) => (b, a)) (back := fun (a, b) => (b, a))
      ensure (testBackForward swapIso (1, 2)) "BackForward should hold"
  },
  {
    name := "testForwardBack: returns true for swap iso"
    run := do
      let swapIso : Iso' (Int × Int) (Int × Int) :=
        iso (forward := fun (a, b) => (b, a)) (back := fun (a, b) => (b, a))
      ensure (testForwardBack swapIso (1, 2)) "ForwardBack should hold"
  },
  {
    name := "checkLensLaws: passes for lawful lens (10 samples)"
    run := do
      let passed ← checkLensLaws "fstLens" fstLens genTestPair genInt (samples := 10)
      ensure passed "All lens laws should pass"
  },
  {
    name := "checkPrismLaws: passes for somePrism (10 samples)"
    run := do
      let passed ← checkPrismLaws "somePrism'" (somePrism' Int) (genOption genInt) genInt (samples := 10)
      ensure passed "All prism laws should pass"
  },
  {
    name := "checkIsoLaws: passes for swap iso (10 samples)"
    run := do
      let swapIso : Iso' (Int × Int) (Int × Int) :=
        iso (forward := fun (a, b) => (b, a)) (back := fun (a, b) => (b, a))
      let genPairInt := genPair genInt genInt
      let passed ← checkIsoLaws "swapIso" swapIso genPairInt genPairInt (samples := 10)
      ensure passed "All iso laws should pass"
  },
  {
    name := "RandState: generates different values"
    run := do
      let r0 := RandState.mk 12345
      let (v1, r1) := r0.next
      let (v2, r2) := r1.next
      let (v3, _) := r2.next
      ensure (v1 != v2) "First two values should differ"
      ensure (v2 != v3) "Second two values should differ"
      ensure (v1 != v3) "First and third should differ"
  },
  {
    name := "RandState.nextInt: stays in range"
    run := do
      let r0 := RandState.mk 99999
      let mut r := r0
      for _ in [:20] do
        let (v, r') := r.nextInt (-10) 10
        r := r'
        ensure (v >= -10 && v <= 10) s!"Value {v} out of range"
  }
]

/-! ## Tracing Tests -/

def tracingTests : List TestCase := [
  {
    name := "describeOptic: returns description for Lens"
    run := do
      let desc := describeOptic "Lens"
      ensure (desc.containsSubstr "Exactly one") "Should describe single focus"
      ensure (desc.containsSubstr "view") "Should mention view operation"
  },
  {
    name := "describeOptic: returns description for Prism"
    run := do
      let desc := describeOptic "Prism"
      ensure (desc.containsSubstr "Zero or one") "Should describe optional focus"
      ensure (desc.containsSubstr "preview") "Should mention preview operation"
  },
  {
    name := "describeOptic: returns description for Traversal"
    run := do
      let desc := describeOptic "Traversal"
      ensure (desc.containsSubstr "Zero or more") "Should describe multiple foci"
  },
  {
    name := "getCapabilities: Lens has view"
    run := do
      let caps := getCapabilities "Lens"
      ensure caps.view "Lens should support view"
      ensure caps.set "Lens should support set"
      ensure caps.over "Lens should support over"
  },
  {
    name := "getCapabilities: Prism has review but not view"
    run := do
      let caps := getCapabilities "Prism"
      ensure (!caps.view) "Prism should not support view"
      ensure caps.review "Prism should support review"
      ensure caps.preview "Prism should support preview"
  },
  {
    name := "getCapabilities: Traversal has no view"
    run := do
      let caps := getCapabilities "Traversal"
      ensure (!caps.view) "Traversal should not support view"
      ensure (!caps.preview) "Traversal should not support preview"
      ensure caps.traverse "Traversal should support traverse"
  },
  {
    name := "composeTypes: Lens ∘ Lens = Lens"
    run := do
      ensureEq "composition" "Lens" (composeTypes "Lens" "Lens")
  },
  {
    name := "composeTypes: Lens ∘ Prism = AffineTraversal"
    run := do
      ensureEq "composition" "AffineTraversal" (composeTypes "Lens" "Prism")
  },
  {
    name := "composeTypes: Lens ∘ Traversal = Traversal"
    run := do
      ensureEq "composition" "Traversal" (composeTypes "Lens" "Traversal")
  },
  {
    name := "composeTypes: Prism ∘ Lens = AffineTraversal"
    run := do
      ensureEq "composition" "AffineTraversal" (composeTypes "Prism" "Lens")
  },
  {
    name := "composeTypes: Prism ∘ Prism = Prism"
    run := do
      ensureEq "composition" "Prism" (composeTypes "Prism" "Prism")
  },
  {
    name := "composeTypes: Traversal ∘ Lens = Traversal"
    run := do
      ensureEq "composition" "Traversal" (composeTypes "Traversal" "Lens")
  },
  {
    name := "composeTypes: Traversal ∘ Traversal = Traversal"
    run := do
      ensureEq "composition" "Traversal" (composeTypes "Traversal" "Traversal")
  },
  {
    name := "composeTypes: Iso ∘ X = X (identity)"
    run := do
      ensureEq "Iso ∘ Lens" "Lens" (composeTypes "Iso" "Lens")
      ensureEq "Iso ∘ Prism" "Prism" (composeTypes "Iso" "Prism")
      ensureEq "Iso ∘ Traversal" "Traversal" (composeTypes "Iso" "Traversal")
  },
  {
    name := "composeTypes: X ∘ Iso = X (identity)"
    run := do
      ensureEq "Lens ∘ Iso" "Lens" (composeTypes "Lens" "Iso")
      ensureEq "Prism ∘ Iso" "Prism" (composeTypes "Prism" "Iso")
      ensureEq "Traversal ∘ Iso" "Traversal" (composeTypes "Traversal" "Iso")
  },
  {
    name := "capabilitiesToString: formats correctly"
    run := do
      let caps := getCapabilities "Lens"
      let str := capabilitiesToString caps
      ensure (str.containsSubstr "view") "Should contain view"
      ensure (str.containsSubstr "set") "Should contain set"
  },
  {
    name := "traceComposition: runs without error"
    run := do
      -- Just verify it doesn't crash
      traceComposition [("lens1", "Lens"), ("lens2", "Lens")]
      pure ()
  },
  {
    name := "printOpticInfo: runs without error"
    run := do
      -- Just verify it doesn't crash
      printOpticInfo "Lens"
      pure ()
  }
]

/-! ## All Tests -/

def cases : List TestCase :=
  propertyTests ++ tracingTests

end CollimatorTests.Tooling
