import Collimator.Core.Profunctor
import Collimator.Core.Choice
import Collimator.Optics.Types
import Collimator.Concrete.Forget
import Collimator.Concrete.Tagged

namespace Collimator

open Collimator.Core
open Collimator.Concrete

universe u

/--
Construct a prism from a builder and a matcher.

A prism focuses on one case of a sum type (variant), allowing you to
pattern-match to extract a value or construct that variant.

## Parameters
- `build`: Construct a value of the sum type from the focused case
- `split`: Pattern-match on the sum type, returning `Sum.inr a` if the
  focused case is present, or `Sum.inl t` (the unchanged value) otherwise

## Example

```lean
-- Prism for the Some case of Option
def somePrism : Prism' (Option α) α :=
  prism
    (build := some)
    (split := fun opt => match opt with
      | some a => Sum.inr a
      | none => Sum.inl none)

-- Usage:
preview' somePrism (some 42)  -- some 42
preview' somePrism none       -- none
review' somePrism 42          -- some 42
```

## Simpler Alternative

For most cases, `prismFromPartial` is easier to use:

```lean
def somePrism : Prism' (Option α) α :=
  prismFromPartial (match_ := id) (build := some)
```

## Laws

A lawful prism satisfies:
1. **Preview-Review**: `preview p (review p b) = some b` - reviewing then previewing succeeds
2. **Review-Preview**: `preview p s = some a → review p a = s` - if preview succeeds, review reconstructs
-/
def prism {s t a b : Type _}
    (build : b → t) (split : s → Sum t a) : Prism s t a b :=
  fun {P} [Profunctor P] hChoice pab =>
    let _ : Choice P := hChoice
    let right := Choice.right (P := P) (γ := t) pab
    let post : Sum t b → t :=
      Sum.elim (fun t' => t') (fun b' => build b')
    Profunctor.dimap (P := P) split post right

/-- Attempt to extract a focused value with a prism. -/
def preview' {s a : Type _}
    (p : Prism' s a) (x : s) : Option a :=
  let forget : Forget (Option a) a a := fun a => some a
  let result := p.toPrism (P := fun α β => Forget (Option a) α β) inferInstance forget
  result x

/-- Inject a value through a prism. -/
def review' {s t a b : Type _}
    (p : Prism s t a b) (b₀ : b) : t :=
  p.toPrism (P := fun α β => Tagged α β) inferInstance b₀

/--
A prism that always fails to match.

Useful as an identity element when composing prisms with `orElse`,
or when you need a prism that never succeeds.

```lean
preview failing 42  -- none (never matches)
```

Note: `review` on a failing prism will return the default value.
-/
def failing {s a : Type _} [Inhabited s] : Prism' s a :=
  prism
    (build := fun _ => default)
    (split := fun s => Sum.inl s)

/--
Create a prism from a partial function (matcher) and a constructor (builder).

This is often more convenient than using `prism` directly with `Sum`.

```lean
-- Prism for even numbers
def evenPrism : Prism' Int Int := prismFromPartial
  (fun n => if n % 2 == 0 then some n else none)
  id

preview evenPrism 4  -- some 4
preview evenPrism 3  -- none
```
-/
def prismFromPartial {s a : Type _}
    (match_ : s → Option a) (build : a → s) : Prism' s a :=
  prism
    (build := build)
    (split := fun s =>
      match match_ s with
      | some a => Sum.inr a
      | none => Sum.inl s)

end Collimator
