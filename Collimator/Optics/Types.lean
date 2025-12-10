import Collimator.Core.Profunctor
import Collimator.Core.Strong
import Collimator.Core.Choice
import Collimator.Core.Closed
import Collimator.Core.Wandering

namespace Collimator

open Collimator.Core

/-!
# Optic Types

Optics are defined as type aliases for polymorphic functions over profunctors.
This encoding allows standard function composition (`∘`) to work naturally:

```lean
lens1 ∘ lens2  -- composes two lenses
lens ∘ prism   -- composes a lens with a prism (gives AffineTraversal)
```

The profunctor constraints determine what operations each optic supports:
- `Profunctor P` alone: Iso (bidirectional transformation)
- `Strong P`: Lens (product-like access)
- `Choice P`: Prism (sum-like access)
- `Strong P + Choice P`: AffineTraversal (0-or-1 focus)
- `Strong P + Choice P + Wandering P`: Traversal (0-to-many focus)
-/

/--
`Optic C s t a b` quantifies over all profunctors satisfying the constraint `C`.
-/
def Optic (C : (Type → Type → Type) → Prop)
    (s t a b : Type) : Type 1 :=
  ∀ {P : Type → Type → Type} [Profunctor P], C P → P a b → P s t

/--
Isomorphisms are optics constrained only by the profunctor structure.
An iso witnesses that `s` and `a` are isomorphic (and `t` and `b`).
-/
def Iso (s t a b : Type) : Type 1 :=
  ∀ {P : Type → Type → Type} [Profunctor P], P a b → P s t

/--
Lenses require a `Strong` profunctor.
A lens focuses on exactly one `a` inside an `s`.
-/
def Lens (s t a b : Type) : Type 1 :=
  ∀ {P : Type → Type → Type} [Profunctor P] [Strong P], P a b → P s t

/--
Prisms require a `Choice` profunctor.
A prism focuses on an `a` that may or may not be present in `s`.
-/
def Prism (s t a b : Type) : Type 1 :=
  ∀ {P : Type → Type → Type} [Profunctor P] [Choice P], P a b → P s t

/--
Affine traversals require both `Strong` and `Choice`.
An affine traversal focuses on at most one `a` inside an `s`.
-/
def AffineTraversal (s t a b : Type) : Type 1 :=
  ∀ {P : Type → Type → Type} [Profunctor P] [Strong P] [Choice P], P a b → P s t

/--
Traversals require `Strong`, `Choice`, and `Wandering` profunctors.
A traversal focuses on zero or more `a` values inside an `s`.
-/
def Traversal (s t a b : Type) : Type 1 :=
  ∀ {P : Type → Type → Type} [Profunctor P] [Strong P] [Choice P] [Wandering P], P a b → P s t

/--
Folds are read-only optics that require `Strong` and `Choice`.
A fold extracts zero or more `a` values from an `s`.
-/
def Fold (s t a b : Type) : Type 1 :=
  ∀ {P : Type → Type → Type} [Profunctor P] [Strong P] [Choice P], P a b → P s t

/--
Setters are write-only optics that require `Strong`.
A setter modifies zero or more `a` values inside an `s`.
-/
def Setter (s t a b : Type) : Type 1 :=
  ∀ {P : Type → Type → Type} [Profunctor P] [Strong P], P a b → P s t

/-- Monomorphic iso (source and target types are the same). -/
abbrev Iso' (s a : Type) := Iso s s a a

/-- Monomorphic lens (source and target types are the same). -/
abbrev Lens' (s a : Type) := Lens s s a a

/-- Monomorphic prism (source and target types are the same). -/
abbrev Prism' (s a : Type) := Prism s s a a

/-- Monomorphic affine traversal (source and target types are the same). -/
abbrev AffineTraversal' (s a : Type) := AffineTraversal s s a a

/-- Monomorphic traversal (source and target types are the same). -/
abbrev Traversal' (s a : Type) := Traversal s s a a

/-- Monomorphic fold (source and target types are the same). -/
abbrev Fold' (s a : Type) := Fold s s a a

/-- Monomorphic setter (source and target types are the same). -/
abbrev Setter' (s a : Type) := Setter s s a a

/-!
## Optic Hierarchy

The optic types form a subtyping hierarchy based on their profunctor constraints:

```
        Iso
       /   \
    Lens   Prism
       \   /
   AffineTraversal ──→ Fold
         |
     Traversal ──→ Setter
```

With type aliases, this hierarchy is enforced by Lean's type system automatically.
When you compose optics with `∘`, the result type has the union of all constraints:

- `Lens ∘ Lens` = `Lens` (both need Strong)
- `Lens ∘ Prism` = `AffineTraversal` (needs Strong + Choice)
- `Lens ∘ Traversal` = `Traversal` (needs Strong + Choice + Wandering)

No explicit coercion instances are needed!
-/

/-!
## Coercion Functions

While standard function composition handles most cases automatically,
these explicit coercion functions are provided for cases where you need
to explicitly widen an optic's type.
-/

/-- Widen an Iso to a Lens. -/
@[inline] def Iso.toLens {s t a b : Type} (i : Iso s t a b) : Lens s t a b :=
  fun {P} [Profunctor P] [Strong P] => i

/-- Widen an Iso to a Prism. -/
@[inline] def Iso.toPrism {s t a b : Type} (i : Iso s t a b) : Prism s t a b :=
  fun {P} [Profunctor P] [Choice P] => i

/-- Widen an Iso to an AffineTraversal. -/
@[inline] def Iso.toAffine {s t a b : Type} (i : Iso s t a b) : AffineTraversal s t a b :=
  fun {P} [Profunctor P] [Strong P] [Choice P] => i

/-- Widen an Iso to a Traversal. -/
@[inline] def Iso.toTraversal {s t a b : Type} (i : Iso s t a b) : Traversal s t a b :=
  fun {P} [Profunctor P] [Strong P] [Choice P] [Wandering P] => i

/-- Widen a Lens to an AffineTraversal. -/
@[inline] def Lens.toAffine {s t a b : Type} (l : Lens s t a b) : AffineTraversal s t a b :=
  fun {P} [Profunctor P] [Strong P] [Choice P] => l

/-- Widen a Lens to a Traversal. -/
@[inline] def Lens.toTraversal {s t a b : Type} (l : Lens s t a b) : Traversal s t a b :=
  fun {P} [Profunctor P] [Strong P] [Choice P] [Wandering P] => l

/-- Widen a Prism to an AffineTraversal. -/
@[inline] def Prism.toAffine {s t a b : Type} (p : Prism s t a b) : AffineTraversal s t a b :=
  fun {P} [Profunctor P] [Strong P] [Choice P] => p

/-- Widen a Prism to a Traversal. -/
@[inline] def Prism.toTraversal {s t a b : Type} (p : Prism s t a b) : Traversal s t a b :=
  fun {P} [Profunctor P] [Strong P] [Choice P] [Wandering P] => p

/-- Widen an AffineTraversal to a Traversal. -/
@[inline] def AffineTraversal.toTraversal {s t a b : Type} (aff : AffineTraversal s t a b) : Traversal s t a b :=
  fun {P} [Profunctor P] [Strong P] [Choice P] [Wandering P] => aff

end Collimator
