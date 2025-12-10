import Collimator.Core.Profunctor
import Collimator.Optics.Types

namespace Collimator

open Collimator.Core

universe u v w

/--
Create an isomorphism from forward and backward maps.

An isomorphism represents a bidirectional, lossless transformation between
two types. Every iso can be used as a lens (viewing/modifying) or a prism
(constructing/pattern-matching).

## Parameters
- `forward`: Transform from source type to focus type
- `back`: Transform from focus type back to source type

## Example

```lean
-- Isomorphism between Bool and Nat (0/1)
def boolNat : Iso' Bool Nat :=
  iso
    (forward := fun b => if b then 1 else 0)
    (back := fun n => n != 0)

-- String ↔ List Char
def stringChars : Iso' String (List Char) :=
  iso (forward := String.toList) (back := String.mk)

-- Usage with lens operations:
view boolNat true           -- 1
over boolNat (· + 10) false -- true (because 10 != 0)

-- Usage with prism operations:
review boolNat 42           -- true
preview boolNat false       -- some 0
```

## Laws

A lawful isomorphism satisfies:
1. **Back-Forward**: `back (forward s) = s` - round-trip preserves source
2. **Forward-Back**: `forward (back a) = a` - round-trip preserves focus

These laws ensure the transformation is truly bidirectional and lossless.
-/
def iso {s t a b : Type _}
    (forward : s → a) (back : b → t) : Iso s t a b :=
  fun {P : Type u → Type v → Type w} [Profunctor P] =>
    Profunctor.dimap (P := P) forward back

/-- Identity optic. -/
def id {α : Type _} : Iso' α α :=
  iso (s := α) (t := α) (a := α) (b := α)
    (forward := fun x => x) (back := fun x => x)

end Collimator
