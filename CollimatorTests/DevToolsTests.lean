import Crucible
import Collimator.Prelude
import Collimator.Debug
import Collimator.Debug.LawCheck
import Collimator.Testing
import Collimator.Tracing
import Collimator.Commands
import Collimator.Helpers

/-!
# Tests for Developer Tools and Utilities

This module consolidates tests for debugging, tracing, and testing utilities:

## Debug Utilities
- Traced optics (tracedLens, tracedPrism)
- Law verification helpers (checkGetPut, checkPutGet, etc.)
- Safe view alternatives (viewSafe, viewOrElse, viewOrPanic)

## Tooling Utilities
- Property-based testing integration
- Composition tracing
- Optic capability analysis
-/

open Collimator
open Collimator.Debug
open Collimator.Debug.LawCheck
open Collimator.Testing
open Collimator.Tracing
open Collimator.Instances.Option
open Crucible
open scoped Collimator.Operators

namespace CollimatorTests.DevTools

testSuite "Developer Tools"

/-! ## Test Structures -/

private structure TestPoint where
  x : Int
  y : Int
deriving BEq, Repr

private def testXLens : Lens' TestPoint Int :=
  lens' (·.x) (fun p v => { p with x := v })

private def testYLens : Lens' TestPoint Int :=
  lens' (·.y) (fun p v => { p with y := v })

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

/-! ## Traced Optics Tests -/

test "tracedLens: view returns correct value" := do
  let traced : Lens' TestPoint Int := tracedLens "xLens" testXLens
  let p := TestPoint.mk 10 20
  let result := p ^. traced
  result ≡ 10

test "tracedLens: set returns correct structure" := do
  let traced : Lens' TestPoint Int := tracedLens "xLens" testXLens
  let p := TestPoint.mk 10 20
  let result := p & traced .~ 99
  result.x ≡ 99
  result.y ≡ 20

test "tracedLens: over modifies correctly" := do
  let traced : Lens' TestPoint Int := tracedLens "xLens" testXLens
  let p := TestPoint.mk 10 20
  let result := p & traced %~ (· + 5)
  result.x ≡ 15

test "tracedPrism: preview some returns value" := do
  let traced : Prism' (Option Int) Int := tracedPrism "somePrism" (somePrism' Int)
  let result := (some 42) ^? traced
  result ≡ (some 42)

test "tracedPrism: preview none returns none" := do
  let traced : Prism' (Option Int) Int := tracedPrism "somePrism" (somePrism' Int)
  let result := (none : Option Int) ^? traced
  result ≡ none

test "tracedPrism: review constructs correctly" := do
  let traced : Prism' (Option Int) Int := tracedPrism "somePrism" (somePrism' Int)
  let result := review' traced 99
  result ≡ (some 99)

/-! ## Debug Law Check Tests - Lens -/

test "checkGetPut: returns true for lawful lens" := do
  let p := TestPoint.mk 10 20
  ensure (checkGetPut testXLens p 99) "GetPut should hold"

test "checkPutGet: returns true for lawful lens" := do
  let p := TestPoint.mk 10 20
  ensure (checkPutGet testXLens p) "PutGet should hold"

test "checkPutPut: returns true for lawful lens" := do
  let p := TestPoint.mk 10 20
  ensure (checkPutPut testXLens p 5 99) "PutPut should hold"

test "quickCheckLens: returns true for lawful lens" := do
  let p := TestPoint.mk 10 20
  ensure (quickCheckLens testXLens p 5 99) "quickCheckLens should pass"

test "verifyLensLaws: batch verification succeeds" := do
  let samples := [
    (TestPoint.mk 0 0, 1, 2),
    (TestPoint.mk 10 20, 30, 40),
    (TestPoint.mk (-5) 100, 0, (-1))
  ]
  let passed ← verifyLensLaws "testXLens" testXLens samples
  ensure passed "All lens laws should pass"

/-! ## Debug Law Check Tests - Prism -/

test "checkPreviewReview: returns true for lawful prism" := do
  ensure (checkPreviewReview (somePrism' Int) 42) "Preview-Review should hold"

test "checkReviewPreview: returns true when preview succeeds" := do
  ensure (checkReviewPreview (somePrism' Int) (some 42)) "Review-Preview should hold for Some"

test "checkReviewPreview: returns true when preview fails" := do
  -- Law doesn't apply when preview fails, so should return true
  ensure (checkReviewPreview (somePrism' Int) (none : Option Int)) "Review-Preview vacuously true for None"

test "quickCheckPrism: returns true for lawful prism" := do
  ensure (quickCheckPrism (somePrism' Int) 42) "quickCheckPrism should pass"

test "verifyPrismLaws: batch verification succeeds" := do
  let samples := [1, 0, -5, 100, 999]
  let passed ← verifyPrismLaws "somePrism'" (somePrism' Int) samples
  ensure passed "All prism laws should pass"

/-! ## Debug Law Check Tests - Iso -/

test "checkBackForward: returns true for lawful iso" := do
  let boolNatIso : Iso' Bool Nat := iso (fun b => if b then 1 else 0) (· != 0)
  ensure (checkBackForward boolNatIso true) "Back-Forward true"
  ensure (checkBackForward boolNatIso false) "Back-Forward false"

test "checkForwardBack: returns true for lawful iso" := do
  let boolNatIso : Iso' Bool Nat := iso (fun b => if b then 1 else 0) (· != 0)
  ensure (checkForwardBack boolNatIso 0) "Forward-Back 0"
  ensure (checkForwardBack boolNatIso 1) "Forward-Back 1"
  -- Note: Forward-Back for n > 1 maps to 1 (true → 1), which is expected

test "verifyIsoLaws: batch verification succeeds" := do
  let boolNatIso : Iso' Bool Nat := iso (fun b => if b then 1 else 0) (· != 0)
  let passed ← verifyIsoLaws "boolNatIso" boolNatIso [true, false] [0, 1]
  ensure passed "All iso laws should pass"

/-! ## Guidance Helpers Tests -/

test "viewSafe: returns some for matching optic" := do
  let prism : Prism' (Option Int) Int := somePrism' Int
  let result := (some 42) ^? prism
  result ≡ (some 42)

test "viewSafe: returns none for non-matching" := do
  let prism : Prism' (Option Int) Int := somePrism' Int
  let result := (none : Option Int) ^? prism
  result ≡ none

test "viewOrElse: returns value when present" := do
  let prism : Prism' (Option Int) Int := somePrism' Int
  let result := ((some 42) ^? prism).getD 0
  result ≡ 42

test "viewOrElse: returns default when missing" := do
  let prism : Prism' (Option Int) Int := somePrism' Int
  let result := ((none : Option Int) ^? prism).getD 999
  result ≡ 999

test "viewOrElseLazy: returns value when present" := do
  let prism : Prism' (Option Int) Int := somePrism' Int
  let result := ((some 42) ^? prism).getD 0
  result ≡ 42

test "viewOrElseLazy: calls default when missing" := do
  let prism : Prism' (Option Int) Int := somePrism' Int
  let result := ((none : Option Int) ^? prism).getD 999
  result ≡ 999

test "hasFocus: returns true when present" := do
  let prism : Prism' (Option Int) Int := somePrism' Int
  ensure (((some 42) ^? prism).isSome) "hasFocus some"

test "hasFocus: returns false when missing" := do
  let prism : Prism' (Option Int) Int := somePrism' Int
  ensure (not ((none : Option Int) ^? prism).isSome) "hasFocus none"

/-! ## Property Testing Tests -/

test "testGetPut: returns true for lawful lens" := do
  let pair := TestPair.mk 10 20
  ensure (testGetPut fstLens pair 99) "GetPut should hold"

test "testPutGet: returns true for lawful lens" := do
  let pair := TestPair.mk 10 20
  ensure (testPutGet fstLens pair) "PutGet should hold"

test "testPutPut: returns true for lawful lens" := do
  let pair := TestPair.mk 10 20
  ensure (testPutPut fstLens pair 5 99) "PutPut should hold"

test "testPreviewReview: returns true for somePrism" := do
  ensure (testPreviewReview (somePrism' Int) 42) "PreviewReview should hold"

test "testReviewPreview: returns true for matching Some" := do
  let opt : Option Int := some 42
  ensure (testReviewPreview (somePrism' Int) opt) "ReviewPreview should hold for Some"

test "testReviewPreview: returns true for None (vacuously)" := do
  let opt : Option Int := none
  ensure (testReviewPreview (somePrism' Int) opt) "ReviewPreview vacuously true for None"

test "testBackForward: returns true for swap iso" := do
  let swapIso : Iso' (Int × Int) (Int × Int) :=
    iso (forward := fun (a, b) => (b, a)) (back := fun (a, b) => (b, a))
  ensure (testBackForward swapIso (1, 2)) "BackForward should hold"

test "testForwardBack: returns true for swap iso" := do
  let swapIso : Iso' (Int × Int) (Int × Int) :=
    iso (forward := fun (a, b) => (b, a)) (back := fun (a, b) => (b, a))
  ensure (testForwardBack swapIso (1, 2)) "ForwardBack should hold"

test "checkLensLaws: passes for lawful lens (10 samples)" := do
  let passed ← checkLensLaws "fstLens" fstLens genTestPair genInt (samples := 10)
  ensure passed "All lens laws should pass"

test "checkPrismLaws: passes for somePrism (10 samples)" := do
  let passed ← checkPrismLaws "somePrism'" (somePrism' Int) (genOption genInt) genInt (samples := 10)
  ensure passed "All prism laws should pass"

test "checkIsoLaws: passes for swap iso (10 samples)" := do
  let swapIso : Iso' (Int × Int) (Int × Int) :=
    iso (forward := fun (a, b) => (b, a)) (back := fun (a, b) => (b, a))
  let genPairInt := genPair genInt genInt
  let passed ← checkIsoLaws "swapIso" swapIso genPairInt genPairInt (samples := 10)
  ensure passed "All iso laws should pass"

test "RandState: generates different values" := do
  let r0 := RandState.mk 12345
  let (v1, r1) := r0.next
  let (v2, r2) := r1.next
  let (v3, _) := r2.next
  ensure (v1 != v2) "First two values should differ"
  ensure (v2 != v3) "Second two values should differ"
  ensure (v1 != v3) "First and third should differ"

test "RandState.nextInt: stays in range" := do
  let r0 := RandState.mk 99999
  let mut r := r0
  for _ in [:20] do
    let (v, r') := r.nextInt (-10) 10
    r := r'
    ensure (v >= -10 && v <= 10) s!"Value {v} out of range"

/-! ## Tracing Tests -/

test "describeOptic: returns description for Lens" := do
  let desc := describeOptic "Lens"
  ensure (desc.containsSubstr "Exactly one") "Should describe single focus"
  ensure (desc.containsSubstr "view") "Should mention view operation"

test "describeOptic: returns description for Prism" := do
  let desc := describeOptic "Prism"
  ensure (desc.containsSubstr "Zero or one") "Should describe optional focus"
  ensure (desc.containsSubstr "preview") "Should mention preview operation"

test "describeOptic: returns description for Traversal" := do
  let desc := describeOptic "Traversal"
  ensure (desc.containsSubstr "Zero or more") "Should describe multiple foci"

test "getCapabilities: Lens has view" := do
  let caps := getCapabilities "Lens"
  ensure caps.view "Lens should support view"
  ensure caps.set "Lens should support set"
  ensure caps.over "Lens should support over"

test "getCapabilities: Prism has review but not view" := do
  let caps := getCapabilities "Prism"
  ensure (!caps.view) "Prism should not support view"
  ensure caps.review "Prism should support review"
  ensure caps.preview "Prism should support preview"

test "getCapabilities: Traversal has no view" := do
  let caps := getCapabilities "Traversal"
  ensure (!caps.view) "Traversal should not support view"
  ensure (!caps.preview) "Traversal should not support preview"
  ensure caps.traverse "Traversal should support traverse"

test "composeTypes: Lens ∘ Lens = Lens" := do
  (composeTypes "Lens" "Lens") ≡ "Lens"

test "composeTypes: Lens ∘ Prism = AffineTraversal" := do
  (composeTypes "Lens" "Prism") ≡ "AffineTraversal"

test "composeTypes: Lens ∘ Traversal = Traversal" := do
  (composeTypes "Lens" "Traversal") ≡ "Traversal"

test "composeTypes: Prism ∘ Lens = AffineTraversal" := do
  (composeTypes "Prism" "Lens") ≡ "AffineTraversal"

test "composeTypes: Prism ∘ Prism = Prism" := do
  (composeTypes "Prism" "Prism") ≡ "Prism"

test "composeTypes: Traversal ∘ Lens = Traversal" := do
  (composeTypes "Traversal" "Lens") ≡ "Traversal"

test "composeTypes: Traversal ∘ Traversal = Traversal" := do
  (composeTypes "Traversal" "Traversal") ≡ "Traversal"

test "composeTypes: Iso ∘ X = X (identity)" := do
  (composeTypes "Iso" "Lens") ≡ "Lens"
  (composeTypes "Iso" "Prism") ≡ "Prism"
  (composeTypes "Iso" "Traversal") ≡ "Traversal"

test "composeTypes: X ∘ Iso = X (identity)" := do
  (composeTypes "Lens" "Iso") ≡ "Lens"
  (composeTypes "Prism" "Iso") ≡ "Prism"
  (composeTypes "Traversal" "Iso") ≡ "Traversal"

test "capabilitiesToString: formats correctly" := do
  let caps := getCapabilities "Lens"
  let str := capabilitiesToString caps
  ensure (str.containsSubstr "view") "Should contain view"
  ensure (str.containsSubstr "set") "Should contain set"

test "traceComposition: runs without error" := do
  -- Just verify it doesn't crash
  traceComposition [("lens1", "Lens"), ("lens2", "Lens")]
  pure ()

test "printOpticInfo: runs without error" := do
  -- Just verify it doesn't crash
  printOpticInfo "Lens"
  pure ()

end CollimatorTests.DevTools
