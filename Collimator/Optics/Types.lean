import Collimator.Core.Profunctor
import Collimator.Core.Strong
import Collimator.Core.Choice
import Collimator.Core.Closed
import Collimator.Core.Wandering

namespace Collimator

open Collimator.Core

/--
`Optic C s t a b` quantifies over all profunctors satisfying the constraint `C`.
-/
def Optic (C : (Type _ → Type _ → Type _) → Type _)
    (s t a b : Type _) : Type _ :=
  ∀ {P : Type _ → Type _ → Type _} [Profunctor P], C P → P a b → P s t

/-- Isomorphisms are optics constrained only by the profunctor structure. -/
structure Iso (s t a b : Type _) where
  toIso : ∀ {P : Type _ → Type _ → Type _} [Profunctor P], P a b → P s t

/-- Coercion to construct an Iso from its profunctor encoding. -/
instance : Coe (∀ {P : Type _ → Type _ → Type _} [Profunctor P], P a b → P s t)
              (Iso s t a b) where
  coe f := ⟨f⟩

/-- Coercion to apply an Iso as if it were its profunctor encoding. -/
instance : CoeFun (Iso s t a b)
              (fun _ => ∀ {P : Type _ → Type _ → Type _} [Profunctor P], P a b → P s t) where
  coe i := i.toIso

/-- Lenses require a `Strong` profunctor. -/
structure Lens (s t a b : Type _) where
  toLens : ∀ {P : Type _ → Type _ → Type _} [Profunctor P], Strong P → P a b → P s t

/-- Coercion to construct a Lens from its profunctor encoding. -/
instance : Coe (∀ {P : Type _ → Type _ → Type _} [Profunctor P], Strong P → P a b → P s t)
              (Lens s t a b) where
  coe f := ⟨f⟩

/-- Coercion to apply a Lens as if it were its profunctor encoding. -/
instance : CoeFun (Lens s t a b)
              (fun _ => ∀ {P : Type _ → Type _ → Type _} [Profunctor P], Strong P → P a b → P s t) where
  coe l := l.toLens

/-
Prisms require a `Choice` profunctor.
-/
structure Prism (s t a b : Type _) where
  toPrism : ∀ {P : Type _ → Type _ → Type _} [Profunctor P], Choice P → P a b → P s t

/-- Coercion to construct a Prism from its profunctor encoding. -/
instance : Coe (∀ {P : Type _ → Type _ → Type _} [Profunctor P], Choice P → P a b → P s t)
              (Prism s t a b) where
  coe f := ⟨f⟩

/-- Coercion to apply a Prism as if it were its profunctor encoding. -/
instance : CoeFun (Prism s t a b)
              (fun _ => ∀ {P : Type _ → Type _ → Type _} [Profunctor P], Choice P → P a b → P s t) where
  coe p := p.toPrism

/--
Traversals require a `Wandering` profunctor (which itself depends on `Strong`
and `Choice`).
-/
structure Traversal (s t a b : Type _) where
  toTraversal : ∀ {P : Type _ → Type _ → Type _} [Profunctor P] [Strong P] [Choice P],
    Wandering P → P a b → P s t

/-- Coercion to construct a Traversal from its profunctor encoding. -/
instance : Coe (∀ {P : Type _ → Type _ → Type _} [Profunctor P] [Strong P] [Choice P],
                 Wandering P → P a b → P s t)
              (Traversal s t a b) where
  coe f := ⟨f⟩

/-- Coercion to apply a Traversal as if it were its profunctor encoding. -/
instance : CoeFun (Traversal s t a b)
              (fun _ => ∀ {P : Type _ → Type _ → Type _} [Profunctor P] [Strong P] [Choice P],
                        Wandering P → P a b → P s t) where
  coe tr := tr.toTraversal

/-- Folds are read-only optics that rely on both `Strong` and `Choice`. -/
structure Fold (s t a b : Type _) where
  toFold : ∀ {P : Type _ → Type _ → Type _} [Profunctor P], Strong P → Choice P → P a b → P s t

/-- Coercion to construct a Fold from its profunctor encoding. -/
instance : Coe (∀ {P : Type _ → Type _ → Type _} [Profunctor P], Strong P → Choice P → P a b → P s t)
              (Fold s t a b) where
  coe f := ⟨f⟩

/-- Coercion to apply a Fold as if it were its profunctor encoding. -/
instance : CoeFun (Fold s t a b)
              (fun _ => ∀ {P : Type _ → Type _ → Type _} [Profunctor P], Strong P → Choice P → P a b → P s t) where
  coe fld := fld.toFold

/--
Setters are write-only optics constrained only by `Strong` profunctors.
-/
structure Setter (s t a b : Type _) where
  toSetter : ∀ {P : Type _ → Type _ → Type _} [Profunctor P], Strong P → P a b → P s t

/-- Coercion to construct a Setter from its profunctor encoding. -/
instance : Coe (∀ {P : Type _ → Type _ → Type _} [Profunctor P], Strong P → P a b → P s t)
              (Setter s t a b) where
  coe f := ⟨f⟩

/-- Coercion to apply a Setter as if it were its profunctor encoding. -/
instance : CoeFun (Setter s t a b)
              (fun _ => ∀ {P : Type _ → Type _ → Type _} [Profunctor P], Strong P → P a b → P s t) where
  coe st := st.toSetter

/--
Affine traversals update at most one focus and require `Strong` and `Choice`.
-/
structure AffineTraversal (s t a b : Type _) where
  toAffineTraversal : ∀ {P : Type _ → Type _ → Type _} [Profunctor P], Strong P → Choice P → P a b → P s t

/-- Coercion to construct an AffineTraversal from its profunctor encoding. -/
instance : Coe (∀ {P : Type _ → Type _ → Type _} [Profunctor P], Strong P → Choice P → P a b → P s t)
              (AffineTraversal s t a b) where
  coe f := ⟨f⟩

/-- Coercion to apply an AffineTraversal as if it were its profunctor encoding. -/
instance : CoeFun (AffineTraversal s t a b)
              (fun _ => ∀ {P : Type _ → Type _ → Type _} [Profunctor P], Strong P → Choice P → P a b → P s t) where
  coe aff := aff.toAffineTraversal

abbrev Iso' (s a : Type _) := Iso s s a a
abbrev Lens' (s : Type _) (a : Type _) := Lens s s a a
abbrev Prism' (s a : Type _) := Prism s s a a
abbrev Traversal' (s a : Type _) := Traversal s s a a
abbrev Fold' (s a : Type _) := Fold s s a a
abbrev Setter' (s a : Type _) := Setter s s a a
abbrev AffineTraversal' (s a : Type _) := AffineTraversal s s a a

end Collimator
