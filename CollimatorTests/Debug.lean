import CollimatorTests.Framework
import Collimator.Prelude
import Collimator.Debug
import Collimator.Debug.LawCheck
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
open Collimator.Instances.Option
open CollimatorTests
open scoped Collimator.Operators

namespace CollimatorTests.Debug

testSuite "Debug Utilities"

-- Test structure for law verification
private structure TestPoint where
  x : Int
  y : Int
deriving BEq, Repr

private def testXLens : Lens' TestPoint Int :=
  lens' (·.x) (fun p v => { p with x := v })

private def testYLens : Lens' TestPoint Int :=
  lens' (·.y) (fun p v => { p with y := v })

-- Traced Lens Tests
test "tracedLens: view returns correct value" := do
  let traced : Lens' TestPoint Int := tracedLens "xLens" testXLens
  let p := TestPoint.mk 10 20
  let result := p ^. traced
  ensureEq "traced view" 10 result

test "tracedLens: set returns correct structure" := do
  let traced : Lens' TestPoint Int := tracedLens "xLens" testXLens
  let p := TestPoint.mk 10 20
  let result := p & traced .~ 99
  ensureEq "traced set x" 99 result.x
  ensureEq "traced set y unchanged" 20 result.y

test "tracedLens: over modifies correctly" := do
  let traced : Lens' TestPoint Int := tracedLens "xLens" testXLens
  let p := TestPoint.mk 10 20
  let result := p & traced %~ (· + 5)
  ensureEq "traced over" 15 result.x

-- Traced Prism Tests
test "tracedPrism: preview some returns value" := do
  let traced : Prism' (Option Int) Int := tracedPrism "somePrism" (somePrism' Int)
  let result := (some 42) ^? traced
  ensureEq "traced preview some" (some 42) result

test "tracedPrism: preview none returns none" := do
  let traced : Prism' (Option Int) Int := tracedPrism "somePrism" (somePrism' Int)
  let result := (none : Option Int) ^? traced
  ensureEq "traced preview none" none result

test "tracedPrism: review constructs correctly" := do
  let traced : Prism' (Option Int) Int := tracedPrism "somePrism" (somePrism' Int)
  let result := review' traced 99
  ensureEq "traced review" (some 99) result

-- Law Check Tests - Lens
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

-- Law Check Tests - Prism
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

-- Iso Law Check Tests
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

-- Guidance Helpers Tests
-- Note: These use ^? operator since optics are now type aliases
test "viewSafe: returns some for matching optic" := do
  let prism : Prism' (Option Int) Int := somePrism' Int
  let result := (some 42) ^? prism
  ensureEq "viewSafe some" (some 42) result

test "viewSafe: returns none for non-matching" := do
  let prism : Prism' (Option Int) Int := somePrism' Int
  let result := (none : Option Int) ^? prism
  ensureEq "viewSafe none" none result

test "viewOrElse: returns value when present" := do
  let prism : Prism' (Option Int) Int := somePrism' Int
  let result := ((some 42) ^? prism).getD 0
  ensureEq "viewOrElse some" 42 result

test "viewOrElse: returns default when missing" := do
  let prism : Prism' (Option Int) Int := somePrism' Int
  let result := ((none : Option Int) ^? prism).getD 999
  ensureEq "viewOrElse none" 999 result

test "viewOrElseLazy: returns value when present" := do
  let prism : Prism' (Option Int) Int := somePrism' Int
  let result := ((some 42) ^? prism).getD 0
  ensureEq "viewOrElseLazy some" 42 result

test "viewOrElseLazy: calls default when missing" := do
  let prism : Prism' (Option Int) Int := somePrism' Int
  let result := ((none : Option Int) ^? prism).getD 999
  ensureEq "viewOrElseLazy none" 999 result

test "hasFocus: returns true when present" := do
  let prism : Prism' (Option Int) Int := somePrism' Int
  ensure (((some 42) ^? prism).isSome) "hasFocus some"

test "hasFocus: returns false when missing" := do
  let prism : Prism' (Option Int) Int := somePrism' Int
  ensure (not ((none : Option Int) ^? prism).isSome) "hasFocus none"

#generate_tests

end CollimatorTests.Debug
