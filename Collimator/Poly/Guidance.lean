import Collimator.Poly.Classes

/-!
# Error Guidance and Safe Helpers

This module provides:
1. **Error message templates** - Clear explanations for common optic misuses
2. **Safe alternatives** - Functions that gracefully handle missing values

## Common Mistakes

- Using `view` on a Prism (use `preview` instead)
- Using `review` on a Lens (use `set` with a source value)
- Forgetting that prisms may fail to match

## Safe Helpers

- `viewSafe` - Like `view` but returns `Option`
- `viewOrElse` - Returns a default on failure
- `viewOrPanic` - Panics with a custom message on failure
-/

namespace Collimator.Poly.Guidance

open Collimator.Poly

/-! ## Error Message Templates -/

/--
Error message explaining why `view` can't be used on a Prism.

Use this to provide helpful guidance when users try invalid operations.
-/
def prismViewError : String :=
  "Cannot use 'view' on a Prism - the pattern might not match!\n" ++
  "Prisms focus on one case of a sum type (Option, Either, etc).\n\n" ++
  "Instead, use:\n" ++
  "  • preview p s  -- returns Option a (safe extraction)\n" ++
  "  • review p a   -- constructs s from a\n\n" ++
  "Example:\n" ++
  "  let result := preview somePrism' myOption\n" ++
  "  match result with\n" ++
  "  | some v => -- handle value\n" ++
  "  | none => -- handle missing"

/--
Error message explaining why `review` can't be used on a Lens.
-/
def lensReviewError : String :=
  "Cannot use 'review' on a Lens - lenses need a source value!\n" ++
  "Lenses focus on exactly one part of a larger structure.\n\n" ++
  "Instead, use:\n" ++
  "  • set l v s    -- replace focus in s with v\n" ++
  "  • over l f s   -- modify focus in s with f\n\n" ++
  "If you need to construct without a source, consider:\n" ++
  "  • Use a Prism or Iso instead\n" ++
  "  • Provide a default source value"

/--
Error message for traversal operations on empty containers.
-/
def emptyTraversalWarning : String :=
  "Traversal found no elements to focus on.\n" ++
  "This is normal behavior - traversals can have zero foci.\n\n" ++
  "If you expected elements:\n" ++
  "  • Check if the container is empty\n" ++
  "  • Verify the traversal targets the right level\n" ++
  "  • Use 'toListOf' to see what's being focused"

/--
Error message when affine traversal fails.
-/
def affineMissError : String :=
  "AffineTraversal failed to find a focus.\n" ++
  "This means the optional element was not present.\n\n" ++
  "This can happen with:\n" ++
  "  • Empty lists (_head, _last)\n" ++
  "  • Out-of-bounds index access (at, ix)\n" ++
  "  • Non-matching sum type variants\n\n" ++
  "Use 'preview' to safely check presence first."

/-! ## Optic Capability Reference -/

/--
Reference string showing which operations work with which optics.
-/
def capabilityMatrix : String :=
  "Optic Capabilities:\n" ++
  "─────────────────────────────────────────────────────────────\n" ++
  "Optic            │ view │ over │ set │ preview │ review │\n" ++
  "─────────────────│──────│──────│─────│─────────│────────│\n" ++
  "Iso              │  ✓   │  ✓   │  ✓  │    ✓    │   ✓    │\n" ++
  "Lens             │  ✓   │  ✓   │  ✓  │    ✓    │        │\n" ++
  "Prism            │      │  ✓   │  ✓  │    ✓    │   ✓    │\n" ++
  "AffineTraversal  │      │  ✓   │  ✓  │    ✓    │        │\n" ++
  "Traversal        │      │  ✓   │  ✓  │         │        │\n" ++
  "Fold             │      │      │     │         │        │\n" ++
  "Setter           │      │  ✓   │  ✓  │         │        │\n" ++
  "─────────────────────────────────────────────────────────────"

/-! ## Safe View Alternatives -/

/--
Safe view that returns `Option` for any optic supporting preview.

This is the preferred way to extract values when you're not sure
if the optic will succeed.

## Example

```lean
-- Works with any optic that has HasPreview
let result := viewSafe myPrism myValue
match result with
| some v => -- use v
| none => -- handle missing
```
-/
def viewSafe {optic : Type _ → Type _ → Type _} {s a : Type _}
    [HasPreview optic] (o : optic s a) (s₀ : s) : Option a :=
  preview o s₀

/--
View with a default value when the optic doesn't match.

## Example

```lean
-- Returns 0 if prism doesn't match
let value := viewOrElse myPrism myValue 0
```
-/
def viewOrElse {optic : Type _ → Type _ → Type _} {s a : Type _}
    [HasPreview optic] (o : optic s a) (s₀ : s) (default : a) : a :=
  match preview o s₀ with
  | some a => a
  | none => default

/--
View with a lazy default (only evaluated on failure).

## Example

```lean
-- computeDefault is only called if prism fails
let value := viewOrElseLazy myPrism myValue (fun _ => computeDefault ())
```
-/
def viewOrElseLazy {optic : Type _ → Type _ → Type _} {s a : Type _}
    [HasPreview optic] (o : optic s a) (s₀ : s) (default : Unit → a) : a :=
  match preview o s₀ with
  | some a => a
  | none => default ()

/--
View or panic with a custom error message.

Use this when you're confident the optic should match,
but want a clear error if it doesn't.

## Example

```lean
-- Panics with message if prism doesn't match
let value := viewOrPanic myPrism myValue "Expected Some but got None"
```
-/
def viewOrPanic {optic : Type _ → Type _ → Type _} {s a : Type _}
    [HasPreview optic] [Inhabited a] (o : optic s a) (s₀ : s) (errMsg : String) : a :=
  match preview o s₀ with
  | some a => a
  | none => panic! errMsg

/--
Check if an optic has a focus in the given source.

## Example

```lean
if hasFocus myPrism myValue then
  -- safe to use preview
else
  -- handle missing
```
-/
def hasFocus {optic : Type _ → Type _ → Type _} {s a : Type _}
    [HasPreview optic] (o : optic s a) (s₀ : s) : Bool :=
  (preview o s₀).isSome

end Collimator.Poly.Guidance
