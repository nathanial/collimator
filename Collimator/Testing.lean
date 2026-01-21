import Collimator.Optics
import Collimator.Theorems.IsoLaws

open Collimator.Theorems

/-!
# Property-Based Testing for Optics

Runtime law verification utilities for optics with random sampling.

## Usage

```lean
import Collimator.Testing

-- Check lens laws with random samples
#eval checkLensLaws "myLens" myLens genPair genInt (samples := 100)

-- Check prism laws
#eval checkPrismLaws "myPrism" myPrism genInt (samples := 100)
```

## What Gets Tested

### Lens Laws
- **GetPut**: `view l (set l v s) = v`
- **PutGet**: `set l (view l s) s = s`
- **PutPut**: `set l v (set l v' s) = set l v s`

### Prism Laws
- **PreviewReview**: `preview p (review p b) = some b`
- **ReviewPreview**: `preview p s = some a → review p a = s`

### Iso Laws
- **BackForward**: `backward (forward x) = x`
- **ForwardBack**: `forward (backward y) = y`
-/

namespace Collimator.Testing

open Collimator

/-! ## Simple Random Generator -/

/-- Simple random state -/
structure RandState where
  rngSeed : UInt64
deriving Inhabited

/-- Get next random value -/
def RandState.next (r : RandState) : UInt64 × RandState :=
  -- Simple LCG: x' = (a * x + c) mod m
  let a : UInt64 := 6364136223846793005
  let c : UInt64 := 1442695040888963407
  let next := a * r.rngSeed + c
  (next, ⟨next⟩)

/-- Get a random Int in a range -/
def RandState.nextInt (r : RandState) (lo hi : Int) : Int × RandState :=
  let (raw, r') := r.next
  let range := hi - lo + 1
  if range <= 0 then (lo, r')
  else
    let n := Int.ofNat (raw.toNat % range.toNat) + lo
    (n, r')

/-- Get a random Nat in a range -/
def RandState.nextNat (r : RandState) (lo hi : Nat) : Nat × RandState :=
  let (raw, r') := r.next
  let range := hi - lo + 1
  if range == 0 then (lo, r')
  else
    let n := raw.toNat % range + lo
    (n, r')

/-- Get a random Bool -/
def RandState.nextBool (r : RandState) : Bool × RandState :=
  let (raw, r') := r.next
  (raw.toNat % 2 == 0, r')

/-! ## Lens Law Testing -/

/-- Test the GetPut law: `view l (set l v s) = v` -/
def testGetPut {S A : Type} [BEq A]
    (l : Lens' S A) (s : S) (v : A) : Bool :=
  view' l (set' l v s) == v

/-- Test the PutGet law: `set l (view l s) s = s` -/
def testPutGet {S A : Type} [BEq S]
    (l : Lens' S A) (s : S) : Bool :=
  set' l (view' l s) s == s

/-- Test the PutPut law: `set l v (set l v' s) = set l v s` -/
def testPutPut {S A : Type} [BEq S]
    (l : Lens' S A) (s : S) (v v' : A) : Bool :=
  set' l v (set' l v' s) == set' l v s

/--
Run property-based tests for all lens laws with a custom generator.
-/
def checkLensLaws {S A : Type} [BEq S] [BEq A] [Repr S] [Repr A]
    (name : String) (l : Lens' S A)
    (genS : RandState → S × RandState)
    (genA : RandState → A × RandState)
    (samples : Nat := 100) : IO Bool := do
  IO.println s!"Testing lens laws for '{name}' ({samples} samples each)..."

  let mut allPassed := true
  let mut rand := RandState.mk 12345

  -- Test GetPut
  IO.print "  GetPut law: "
  let mut getPutPassed := true
  for _ in [:samples] do
    let (s, r1) := genS rand
    let (v, r2) := genA r1
    rand := r2
    unless testGetPut l s v do
      IO.println s!"✗ Counter-example: s={repr s}, v={repr v}"
      getPutPassed := false
      allPassed := false
      break
  if getPutPassed then IO.println "✓"

  -- Test PutGet
  IO.print "  PutGet law: "
  let mut putGetPassed := true
  for _ in [:samples] do
    let (s, r1) := genS rand
    rand := r1
    unless testPutGet l s do
      IO.println s!"✗ Counter-example: s={repr s}"
      putGetPassed := false
      allPassed := false
      break
  if putGetPassed then IO.println "✓"

  -- Test PutPut
  IO.print "  PutPut law: "
  let mut putPutPassed := true
  for _ in [:samples] do
    let (s, r1) := genS rand
    let (v, r2) := genA r1
    let (v', r3) := genA r2
    rand := r3
    unless testPutPut l s v v' do
      IO.println s!"✗ Counter-example: s={repr s}, v={repr v}, v'={repr v'}"
      putPutPassed := false
      allPassed := false
      break
  if putPutPassed then IO.println "✓"

  if allPassed then
    IO.println s!"  All lens laws verified for '{name}'"
  else
    IO.println s!"  Some lens laws FAILED for '{name}'"

  return allPassed

/-! ## Prism Law Testing -/

/-- Test the PreviewReview law: `preview p (review p b) = some b` -/
def testPreviewReview {S A : Type} [BEq A]
    (p : Prism' S A) (b : A) : Bool :=
  preview' p (review' p b) == some b

/-- Test the ReviewPreview law: when preview succeeds, review reconstructs -/
def testReviewPreview {S A : Type} [BEq S]
    (p : Prism' S A) (s : S) : Bool :=
  match preview' p s with
  | some a => review' p a == s
  | none => true  -- Law is vacuously true when preview fails

/--
Run property-based tests for all prism laws.
-/
def checkPrismLaws {S A : Type} [BEq S] [BEq A] [Repr S] [Repr A]
    (name : String) (p : Prism' S A)
    (genS : RandState → S × RandState)
    (genA : RandState → A × RandState)
    (samples : Nat := 100) : IO Bool := do
  IO.println s!"Testing prism laws for '{name}' ({samples} samples each)..."

  let mut allPassed := true
  let mut rand := RandState.mk 54321

  -- Test PreviewReview
  IO.print "  PreviewReview law: "
  let mut previewReviewPassed := true
  for _ in [:samples] do
    let (b, r1) := genA rand
    rand := r1
    unless testPreviewReview p b do
      IO.println s!"✗ Counter-example: b={repr b}"
      previewReviewPassed := false
      allPassed := false
      break
  if previewReviewPassed then IO.println "✓"

  -- Test ReviewPreview
  IO.print "  ReviewPreview law: "
  let mut reviewPreviewPassed := true
  for _ in [:samples] do
    let (s, r1) := genS rand
    rand := r1
    unless testReviewPreview p s do
      IO.println s!"✗ Counter-example: s={repr s}"
      reviewPreviewPassed := false
      allPassed := false
      break
  if reviewPreviewPassed then IO.println "✓"

  if allPassed then
    IO.println s!"  All prism laws verified for '{name}'"
  else
    IO.println s!"  Some prism laws FAILED for '{name}'"

  return allPassed

/-! ## Iso Law Testing -/

/-- Test the BackForward law: `backward (forward x) = x` -/
def testBackForward {S A : Type} [BEq S]
    (i : Iso' S A) (s : S) : Bool :=
  isoBackward i (isoForward i s) == s

/-- Test the ForwardBack law: `forward (backward y) = y` -/
def testForwardBack {S A : Type} [BEq A]
    (i : Iso' S A) (a : A) : Bool :=
  isoForward i (isoBackward i a) == a

/--
Run property-based tests for all iso laws.
-/
def checkIsoLaws {S A : Type} [BEq S] [BEq A] [Repr S] [Repr A]
    (name : String) (i : Iso' S A)
    (genS : RandState → S × RandState)
    (genA : RandState → A × RandState)
    (samples : Nat := 100) : IO Bool := do
  IO.println s!"Testing iso laws for '{name}' ({samples} samples each)..."

  let mut allPassed := true
  let mut rand := RandState.mk 67890

  -- Test BackForward
  IO.print "  BackForward law: "
  let mut backForwardPassed := true
  for _ in [:samples] do
    let (s, r1) := genS rand
    rand := r1
    unless testBackForward i s do
      IO.println s!"✗ Counter-example: s={repr s}"
      backForwardPassed := false
      allPassed := false
      break
  if backForwardPassed then IO.println "✓"

  -- Test ForwardBack
  IO.print "  ForwardBack law: "
  let mut forwardBackPassed := true
  for _ in [:samples] do
    let (a, r1) := genA rand
    rand := r1
    unless testForwardBack i a do
      IO.println s!"✗ Counter-example: a={repr a}"
      forwardBackPassed := false
      allPassed := false
      break
  if forwardBackPassed then IO.println "✓"

  if allPassed then
    IO.println s!"  All iso laws verified for '{name}'"
  else
    IO.println s!"  Some iso laws FAILED for '{name}'"

  return allPassed

/-! ## Common Generators -/

/-- Generate random Int in [-100, 100] -/
def genInt : RandState → Int × RandState :=
  fun r => r.nextInt (-100) 100

/-- Generate random Nat in [0, 100] -/
def genNat : RandState → Nat × RandState :=
  fun r => r.nextNat 0 100

/-- Generate random Bool -/
def genBool : RandState → Bool × RandState :=
  fun r => r.nextBool

/-- Generate random Option from inner generator -/
def genOption {A : Type} (genA : RandState → A × RandState) : RandState → Option A × RandState :=
  fun r =>
    let (b, r1) := r.nextBool
    if b then
      let (a, r2) := genA r1
      (some a, r2)
    else
      (none, r1)

/-- Generate random pair -/
def genPair {A B : Type}
    (genA : RandState → A × RandState)
    (genB : RandState → B × RandState) : RandState → (A × B) × RandState :=
  fun r =>
    let (a, r1) := genA r
    let (b, r2) := genB r1
    ((a, b), r2)

end Collimator.Testing
