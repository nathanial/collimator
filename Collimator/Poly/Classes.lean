import Collimator.Optics

namespace Collimator.Poly


/-!
# Polymorphic Optic Type Classes

This module defines type classes for polymorphic operations on optics,
allowing the same function names (`view`, `over`, `set`, etc.) to work
across different optic types (Iso, Lens, Prism, Traversal, etc.).

## Design

Each type class captures a specific operation:
- `HasView` - extract a value (Iso, Lens)
- `HasOver` - modify focused values (Iso, Lens, Prism, Traversal, etc.)
- `HasSet` - set focused values (Iso, Lens, Prism, Traversal, etc.)
- `HasPreview` - optionally extract a value (Iso, Lens, Prism, AffineTraversal)
- `HasReview` - construct from a value (Iso, Prism)
- `HasTraverse` - traverse with effects (all optic types)

## Usage

```lean
import Collimator.Poly

open Collimator.Poly

-- Works with any optic that supports viewing
def getValue {optic : Type → Type → Type 1} [HasView optic]
    {s a : Type} (o : optic s a) (x : s) : a :=
  view o x

-- Works with any optic that supports over
def increment {optic : Type → Type → Type → Type → Type 1} [HasOver optic]
    {s t : Type} (o : optic s t Int Int) : s → t :=
  over o (· + 1)
```

## Laws

Each type class has associated laws that instances should satisfy:

**HasView**:
- (No specific laws, but typically combined with HasSet for GetPut/PutGet laws)

**HasOver**:
- Identity: `over o id = id`
- Composition: `over o (f ∘ g) = over o f ∘ over o g`

**HasSet**:
- SetSet: `set o v2 (set o v1 s) = set o v2 s`

**HasView + HasSet** (when both present):
- GetPut: `set o (view o s) s = s`
- PutGet: `view o (set o v s) = v`

**HasPreview + HasReview** (when both present):
- Preview-Review: `preview o (review o b) = some b`

**HasTraverse**:
- Identity: `traverse o pure = pure`
- Composition: `traverse o (Compose.mk ∘ map (traverse o g) ∘ f) = Compose.mk ∘ map (traverse o (Compose.mk ∘ map g ∘ f))`

-/

/--
Type class for optics that support viewing (extracting a single value).

Instances: Iso, Lens

# Laws
When combined with `HasSet`:
- GetPut: `set o (view o s) s = s`
- PutGet: `view o (set o v s) = v`
-/
class HasView (optic : Type → Type → Type 1) where
  /-- Extract the focused value from a structure. -/
  view : ∀ {s a : Type}, optic s a → s → a

/--
Type class for optics that support modifying focused values.

Instances: Iso, Lens, Prism, AffineTraversal, Traversal, Setter

# Laws
- Identity: `over o id = id`
- Composition: `over o (f ∘ g) = over o f ∘ over o g`
-/
class HasOver (optic : Type → Type → Type → Type → Type 1) where
  /-- Apply a function to all focused values. -/
  over : ∀ {s t a b : Type}, optic s t a b → (a → b) → s → t

/--
Type class for optics that support setting focused values.

Instances: Iso, Lens, Prism, AffineTraversal, Traversal, Setter

# Laws
- SetSet: `set o v2 (set o v1 s) = set o v2 s`
-/
class HasSet (optic : Type → Type → Type → Type → Type 1) where
  /-- Replace all focused values with a constant. -/
  set : ∀ {s t a b : Type}, optic s t a b → b → s → t

/--
Type class for optics that support optional viewing.

Instances: Iso, Lens, Prism, AffineTraversal

Returns `some a` if the focus exists, `none` otherwise.
-/
class HasPreview (optic : Type → Type → Type 1) where
  /-- Optionally extract a focused value. -/
  preview : ∀ {s a : Type}, optic s a → s → Option a

/--
Type class for optics that support construction (building the whole from a part).

Instances: Iso, Prism

# Laws
When combined with `HasPreview`:
- Preview-Review: `preview o (review o b) = some b`
-/
class HasReview (optic : Type → Type → Type → Type → Type 1) where
  /-- Construct a structure from a focused value. -/
  review : ∀ {s t a b : Type}, optic s t a b → b → t

/--
Type class for optics that support effectful traversal.

Instances: Iso, Lens, Prism, AffineTraversal, Traversal

# Laws
- Identity: `traverse o pure = pure`
- Composition: `Compose (fmap (traverse o g) (traverse o f s)) = traverse o (Compose ∘ fmap g ∘ f) s`
-/
class HasTraverse (optic : Type → Type → Type → Type → Type 1) where
  /-- Traverse focused values with an effectful function. -/
  traverse : ∀ {s t a b : Type} {F : Type → Type} [Applicative F],
    optic s t a b → (a → F b) → s → F t

-- Export all methods for convenient use
export HasView (view)
export HasOver (over)
export HasSet (set)
export HasPreview (preview)
export HasReview (review)
export HasTraverse (traverse)

end Collimator.Poly
