import Collimator.Optics
import Collimator.Theorems.IsoLaws

/-!
# Runtime Law Verification for Optics

This module provides functions to verify optic laws at runtime,
useful for testing custom optics.

## Lens Laws

A lawful lens satisfies:
1. **GetPut**: `view l (set l v s) = v` - setting then viewing returns what was set
2. **PutGet**: `set l (view l s) s = s` - setting the current value is a no-op
3. **PutPut**: `set l v (set l v' s) = set l v s` - setting twice is same as setting once

## Prism Laws

A lawful prism satisfies:
1. **Preview-Review**: `preview p (review p b) = some b` - reviewing then previewing succeeds
2. **Review-Preview**: `preview p s = some a → review p a = s` - if preview succeeds, review reconstructs

## Usage

```lean
import Collimator.Debug.LawCheck

-- Check individual laws
let ok := checkGetPut myLens myStruct myValue

-- Batch verify with sample data
let samples := [(struct1, val1, val2), (struct2, val3, val4)]
let passed ← verifyLensLaws "myLens" myLens samples
```
-/

namespace Collimator.Debug.LawCheck

open Collimator


/-! ## Lens Law Checks -/

/--
Check the GetPut law: `view l (set l v s) = v`

After setting a value `v` into structure `s`, viewing should return `v`.
-/
def checkGetPut {s a : Type} [BEq a] (l : Lens' s a) (s₀ : s) (v : a) : Bool :=
  view' l (set' l v s₀) == v

/--
Check the PutGet law: `set l (view l s) s = s`

Setting the currently-viewed value should be a no-op.
-/
def checkPutGet {s a : Type} [BEq s] (l : Lens' s a) (s₀ : s) : Bool :=
  set' l (view' l s₀) s₀ == s₀

/--
Check the PutPut law: `set l v (set l v' s) = set l v s`

Setting twice with different values is equivalent to setting once with the final value.
-/
def checkPutPut {s a : Type} [BEq s] (l : Lens' s a) (s₀ : s) (v v' : a) : Bool :=
  set' l v (set' l v' s₀) == set' l v s₀

/--
Verify all three lens laws with a list of sample data.

Returns `true` if all laws pass for all samples, `false` otherwise.
Prints diagnostic messages for failures.

## Parameters
- `name`: Name for diagnostic output
- `l`: The lens to verify
- `samples`: List of `(structure, value1, value2)` tuples to test

## Example

```lean
let samples := [
  (Point.mk 0 0, 10, 20),
  (Point.mk 5 5, 0, -1)
]
let passed ← verifyLensLaws "xLens" xLens samples
```
-/
def verifyLensLaws {s a : Type} [BEq s] [BEq a] [Repr s] [Repr a]
    (name : String) (l : Lens' s a) (samples : List (s × a × a)) : IO Bool := do
  let mut allPassed := true
  for (s₀, v, v') in samples do
    unless checkGetPut l s₀ v do
      IO.println s!"  ✗ {name}: GetPut failed for s={repr s₀}, v={repr v}"
      allPassed := false
    unless checkPutGet l s₀ do
      IO.println s!"  ✗ {name}: PutGet failed for s={repr s₀}"
      allPassed := false
    unless checkPutPut l s₀ v v' do
      IO.println s!"  ✗ {name}: PutPut failed for s={repr s₀}, v={repr v}, v'={repr v'}"
      allPassed := false
  if allPassed then
    IO.println s!"  ✓ {name}: All lens laws verified ({samples.length} samples)"
  return allPassed

/--
Quick check all lens laws with a single sample.

Useful for simple sanity checks.
-/
def quickCheckLens {s a : Type} [BEq s] [BEq a]
    (l : Lens' s a) (s₀ : s) (v v' : a) : Bool :=
  checkGetPut l s₀ v && checkPutGet l s₀ && checkPutPut l s₀ v v'

/-! ## Prism Law Checks -/

/--
Check the Preview-Review law: `preview p (review p b) = some b`

Reviewing a value and then previewing should return the original value.
-/
def checkPreviewReview {s a : Type} [BEq a] (p : Prism' s a) (b : a) : Bool :=
  preview' p (review' p b) == some b

/--
Check the Review-Preview law for a specific case where preview succeeds.

If `preview p s = some a`, then `review p a = s`.

Note: This only makes sense when we know preview succeeds.
-/
def checkReviewPreview {s a : Type} [BEq s] (p : Prism' s a) (s₀ : s) : Bool :=
  match preview' p s₀ with
  | some a => review' p a == s₀
  | none => true  -- Law doesn't apply when preview fails

/--
Verify prism laws with a list of focus values.

## Parameters
- `name`: Name for diagnostic output
- `p`: The prism to verify
- `samples`: List of focus values to test with Preview-Review

## Example

```lean
let samples := [1, 2, 3, 0, -5]
let passed ← verifyPrismLaws "somePrism" (somePrism' Int) samples
```
-/
def verifyPrismLaws {s a : Type} [BEq s] [BEq a] [Repr s] [Repr a]
    (name : String) (p : Prism' s a) (samples : List a) : IO Bool := do
  let mut allPassed := true
  for b in samples do
    unless checkPreviewReview p b do
      IO.println s!"  ✗ {name}: Preview-Review failed for b={repr b}"
      allPassed := false
  if allPassed then
    IO.println s!"  ✓ {name}: All prism laws verified ({samples.length} samples)"
  return allPassed

/--
Quick check prism laws with a single sample.
-/
def quickCheckPrism {s a : Type} [BEq s] [BEq a]
    (p : Prism' s a) (b : a) : Bool :=
  checkPreviewReview p b

/-! ## Iso Law Checks -/

/--
Check the Back-Forward law: `back (forward s) = s`

Round-tripping through the iso and back should preserve the source.
-/
def checkBackForward {s a : Type} [BEq s] (i : Iso' s a) (s₀ : s) : Bool :=
  let forward := Collimator.Theorems.isoForward i s₀
  let back := Collimator.Theorems.isoBackward i forward
  back == s₀

/--
Check the Forward-Back law: `forward (back a) = a`

Round-tripping through the iso in reverse should preserve the focus.
-/
def checkForwardBack {s a : Type} [BEq a] (i : Iso' s a) (a₀ : a) : Bool :=
  let back := Collimator.Theorems.isoBackward i a₀
  let forward := Collimator.Theorems.isoForward i back
  forward == a₀

/--
Verify iso laws with sample data.

## Parameters
- `name`: Name for diagnostic output
- `i`: The iso to verify
- `sourceSamples`: Source values to test Back-Forward
- `focusSamples`: Focus values to test Forward-Back
-/
def verifyIsoLaws {s a : Type} [BEq s] [BEq a] [Repr s] [Repr a]
    (name : String) (i : Iso' s a)
    (sourceSamples : List s) (focusSamples : List a) : IO Bool := do
  let mut allPassed := true
  for s₀ in sourceSamples do
    unless checkBackForward i s₀ do
      IO.println s!"  ✗ {name}: Back-Forward failed for s={repr s₀}"
      allPassed := false
  for a₀ in focusSamples do
    unless checkForwardBack i a₀ do
      IO.println s!"  ✗ {name}: Forward-Back failed for a={repr a₀}"
      allPassed := false
  if allPassed then
    let total := sourceSamples.length + focusSamples.length
    IO.println s!"  ✓ {name}: All iso laws verified ({total} samples)"
  return allPassed

end Collimator.Debug.LawCheck
