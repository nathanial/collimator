import CollimatorTests.Framework
import Collimator.Prelude
import Collimator.Debug
import Collimator.Debug.LawCheck
import Collimator.Poly.Guidance
import Collimator.Helpers

/-!
# Tests for Debug Utilities

Tests for:
- Traced optics (tracedLens, tracedPrism)
- Law verification helpers (checkGetPut, checkPutGet, etc.)
- Safe view alternatives (viewSafe, viewOrElse, viewOrPanic)
-/

open Collimator
open Collimator.Debug
open Collimator.Debug.LawCheck
open Collimator.Poly.Guidance
open Collimator.Instances.Option
open CollimatorTests

namespace CollimatorTests.Debug

-- Test structure for law verification
private structure TestPoint where
  x : Int
  y : Int
deriving BEq, Repr

private def testXLens : Lens' TestPoint Int :=
  lens' (·.x) (fun p v => { p with x := v })

private def testYLens : Lens' TestPoint Int :=
  lens' (·.y) (fun p v => { p with y := v })

def cases : List TestCase := [
  -- Traced Lens Tests
  {
    name := "tracedLens: view returns correct value"
    run := do
      let traced := tracedLens "xLens" testXLens
      let p := TestPoint.mk 10 20
      let result := view' traced p
      ensureEq "traced view" 10 result
  },
  {
    name := "tracedLens: set returns correct structure"
    run := do
      let traced := tracedLens "xLens" testXLens
      let p := TestPoint.mk 10 20
      let result := set' traced 99 p
      ensureEq "traced set x" 99 result.x
      ensureEq "traced set y unchanged" 20 result.y
  },
  {
    name := "tracedLens: over modifies correctly"
    run := do
      let traced := tracedLens "xLens" testXLens
      let p := TestPoint.mk 10 20
      let result := over' traced (· + 5) p
      ensureEq "traced over" 15 result.x
  },

  -- Traced Prism Tests
  {
    name := "tracedPrism: preview some returns value"
    run := do
      let traced := tracedPrism "somePrism" (somePrism' Int)
      let result := preview' traced (some 42)
      ensureEq "traced preview some" (some 42) result
  },
  {
    name := "tracedPrism: preview none returns none"
    run := do
      let traced := tracedPrism "somePrism" (somePrism' Int)
      let result := preview' traced (none : Option Int)
      ensureEq "traced preview none" none result
  },
  {
    name := "tracedPrism: review constructs correctly"
    run := do
      let traced := tracedPrism "somePrism" (somePrism' Int)
      let result := review' traced 99
      ensureEq "traced review" (some 99) result
  },

  -- Law Check Tests - Lens
  {
    name := "checkGetPut: returns true for lawful lens"
    run := do
      let p := TestPoint.mk 10 20
      ensure (checkGetPut testXLens p 99) "GetPut should hold"
  },
  {
    name := "checkPutGet: returns true for lawful lens"
    run := do
      let p := TestPoint.mk 10 20
      ensure (checkPutGet testXLens p) "PutGet should hold"
  },
  {
    name := "checkPutPut: returns true for lawful lens"
    run := do
      let p := TestPoint.mk 10 20
      ensure (checkPutPut testXLens p 5 99) "PutPut should hold"
  },
  {
    name := "quickCheckLens: returns true for lawful lens"
    run := do
      let p := TestPoint.mk 10 20
      ensure (quickCheckLens testXLens p 5 99) "quickCheckLens should pass"
  },
  {
    name := "verifyLensLaws: batch verification succeeds"
    run := do
      let samples := [
        (TestPoint.mk 0 0, 1, 2),
        (TestPoint.mk 10 20, 30, 40),
        (TestPoint.mk (-5) 100, 0, (-1))
      ]
      let passed ← verifyLensLaws "testXLens" testXLens samples
      ensure passed "All lens laws should pass"
  },

  -- Law Check Tests - Prism
  {
    name := "checkPreviewReview: returns true for lawful prism"
    run := do
      ensure (checkPreviewReview (somePrism' Int) 42) "Preview-Review should hold"
  },
  {
    name := "checkReviewPreview: returns true when preview succeeds"
    run := do
      ensure (checkReviewPreview (somePrism' Int) (some 42)) "Review-Preview should hold for Some"
  },
  {
    name := "checkReviewPreview: returns true when preview fails"
    run := do
      -- Law doesn't apply when preview fails, so should return true
      ensure (checkReviewPreview (somePrism' Int) (none : Option Int)) "Review-Preview vacuously true for None"
  },
  {
    name := "quickCheckPrism: returns true for lawful prism"
    run := do
      ensure (quickCheckPrism (somePrism' Int) 42) "quickCheckPrism should pass"
  },
  {
    name := "verifyPrismLaws: batch verification succeeds"
    run := do
      let samples := [1, 0, -5, 100, 999]
      let passed ← verifyPrismLaws "somePrism'" (somePrism' Int) samples
      ensure passed "All prism laws should pass"
  },

  -- Iso Law Check Tests
  {
    name := "checkBackForward: returns true for lawful iso"
    run := do
      let boolNatIso : Iso' Bool Nat := iso (fun b => if b then 1 else 0) (· != 0)
      ensure (checkBackForward boolNatIso true) "Back-Forward true"
      ensure (checkBackForward boolNatIso false) "Back-Forward false"
  },
  {
    name := "checkForwardBack: returns true for lawful iso"
    run := do
      let boolNatIso : Iso' Bool Nat := iso (fun b => if b then 1 else 0) (· != 0)
      ensure (checkForwardBack boolNatIso 0) "Forward-Back 0"
      ensure (checkForwardBack boolNatIso 1) "Forward-Back 1"
      -- Note: Forward-Back for n > 1 maps to 1 (true → 1), which is expected
  },
  {
    name := "verifyIsoLaws: batch verification succeeds"
    run := do
      let boolNatIso : Iso' Bool Nat := iso (fun b => if b then 1 else 0) (· != 0)
      let passed ← verifyIsoLaws "boolNatIso" boolNatIso [true, false] [0, 1]
      ensure passed "All iso laws should pass"
  },

  -- Guidance Helpers Tests
  {
    name := "viewSafe: returns some for matching optic"
    run := do
      let result := viewSafe (somePrism' Int) (some 42)
      ensureEq "viewSafe some" (some 42) result
  },
  {
    name := "viewSafe: returns none for non-matching"
    run := do
      let result := viewSafe (somePrism' Int) (none : Option Int)
      ensureEq "viewSafe none" none result
  },
  {
    name := "viewOrElse: returns value when present"
    run := do
      let result := viewOrElse (somePrism' Int) (some 42) 0
      ensureEq "viewOrElse some" 42 result
  },
  {
    name := "viewOrElse: returns default when missing"
    run := do
      let result := viewOrElse (somePrism' Int) (none : Option Int) 999
      ensureEq "viewOrElse none" 999 result
  },
  {
    name := "viewOrElseLazy: returns value when present"
    run := do
      let result := viewOrElseLazy (somePrism' Int) (some 42) (fun _ => 0)
      ensureEq "viewOrElseLazy some" 42 result
  },
  {
    name := "viewOrElseLazy: calls default when missing"
    run := do
      let result := viewOrElseLazy (somePrism' Int) (none : Option Int) (fun _ => 999)
      ensureEq "viewOrElseLazy none" 999 result
  },
  {
    name := "hasFocus: returns true when present"
    run := do
      ensure (hasFocus (somePrism' Int) (some 42)) "hasFocus some"
  },
  {
    name := "hasFocus: returns false when missing"
    run := do
      ensure (not (hasFocus (somePrism' Int) (none : Option Int))) "hasFocus none"
  },

  -- Error Message Tests (just verify strings are non-empty)
  {
    name := "prismViewError: provides helpful message"
    run := do
      ensure (prismViewError.length > 50) "prismViewError should have content"
      ensure (prismViewError.containsSubstr "preview") "prismViewError mentions preview"
  },
  {
    name := "lensReviewError: provides helpful message"
    run := do
      ensure (lensReviewError.length > 50) "lensReviewError should have content"
      ensure (lensReviewError.containsSubstr "set") "lensReviewError mentions set"
  },
  {
    name := "capabilityMatrix: provides reference"
    run := do
      ensure (capabilityMatrix.length > 100) "capabilityMatrix should have content"
      ensure (capabilityMatrix.containsSubstr "Lens") "capabilityMatrix mentions Lens"
      ensure (capabilityMatrix.containsSubstr "Prism") "capabilityMatrix mentions Prism"
  }
]

end CollimatorTests.Debug
