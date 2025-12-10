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
def Optic (C : (Type → Type → Type) → Prop)
    (s t a b : Type) : Type 1 :=
  ∀ {P : Type → Type → Type} [Profunctor P], C P → P a b → P s t

/-- Isomorphisms are optics constrained only by the profunctor structure. -/
structure Iso (s t a b : Type) : Type 1 where
  toIso : ∀ {P : Type → Type → Type} [Profunctor P], P a b → P s t

/-- Coercion to construct an Iso from its profunctor encoding. -/
instance : Coe (∀ {P : Type → Type → Type} [Profunctor P], P a b → P s t)
              (Iso s t a b) where
  coe f := ⟨f⟩

/-- Coercion to apply an Iso as if it were its profunctor encoding. -/
instance : CoeFun (Iso s t a b)
              (fun _ => ∀ {P : Type → Type → Type} [Profunctor P], P a b → P s t) where
  coe i := i.toIso

/-- Lenses require a `Strong` profunctor. -/
structure Lens (s t a b : Type) : Type 1 where
  toLens : ∀ {P : Type → Type → Type} [Profunctor P], Strong P → P a b → P s t

/-- Coercion to construct a Lens from its profunctor encoding. -/
instance : Coe (∀ {P : Type → Type → Type} [Profunctor P], Strong P → P a b → P s t)
              (Lens s t a b) where
  coe f := ⟨f⟩

/-- Coercion to apply a Lens as if it were its profunctor encoding. -/
instance : CoeFun (Lens s t a b)
              (fun _ => ∀ {P : Type → Type → Type} [Profunctor P], Strong P → P a b → P s t) where
  coe l := l.toLens

/-
Prisms require a `Choice` profunctor.
-/
structure Prism (s t a b : Type) : Type 1 where
  toPrism : ∀ {P : Type → Type → Type} [Profunctor P], Choice P → P a b → P s t

/-- Coercion to construct a Prism from its profunctor encoding. -/
instance : Coe (∀ {P : Type → Type → Type} [Profunctor P], Choice P → P a b → P s t)
              (Prism s t a b) where
  coe f := ⟨f⟩

/-- Coercion to apply a Prism as if it were its profunctor encoding. -/
instance : CoeFun (Prism s t a b)
              (fun _ => ∀ {P : Type → Type → Type} [Profunctor P], Choice P → P a b → P s t) where
  coe p := p.toPrism

/--
Traversals require a `Wandering` profunctor (which itself depends on `Strong`
and `Choice`).
-/
structure Traversal (s t a b : Type) : Type 1 where
  toTraversal : ∀ {P : Type → Type → Type} [Profunctor P] [Strong P] [Choice P],
    Wandering P → P a b → P s t

/-- Coercion to construct a Traversal from its profunctor encoding. -/
instance : Coe (∀ {P : Type → Type → Type} [Profunctor P] [Strong P] [Choice P],
                 Wandering P → P a b → P s t)
              (Traversal s t a b) where
  coe f := ⟨f⟩

/-- Coercion to apply a Traversal as if it were its profunctor encoding. -/
instance : CoeFun (Traversal s t a b)
              (fun _ => ∀ {P : Type → Type → Type} [Profunctor P] [Strong P] [Choice P],
                        Wandering P → P a b → P s t) where
  coe tr := tr.toTraversal

/-- Folds are read-only optics that rely on both `Strong` and `Choice`. -/
structure Fold (s t a b : Type) : Type 1 where
  toFold : ∀ {P : Type → Type → Type} [Profunctor P], Strong P → Choice P → P a b → P s t

/-- Coercion to construct a Fold from its profunctor encoding. -/
instance : Coe (∀ {P : Type → Type → Type} [Profunctor P], Strong P → Choice P → P a b → P s t)
              (Fold s t a b) where
  coe f := ⟨f⟩

/-- Coercion to apply a Fold as if it were its profunctor encoding. -/
instance : CoeFun (Fold s t a b)
              (fun _ => ∀ {P : Type → Type → Type} [Profunctor P], Strong P → Choice P → P a b → P s t) where
  coe fld := fld.toFold

/--
Setters are write-only optics constrained only by `Strong` profunctors.
-/
structure Setter (s t a b : Type) : Type 1 where
  toSetter : ∀ {P : Type → Type → Type} [Profunctor P], Strong P → P a b → P s t

/-- Coercion to construct a Setter from its profunctor encoding. -/
instance : Coe (∀ {P : Type → Type → Type} [Profunctor P], Strong P → P a b → P s t)
              (Setter s t a b) where
  coe f := ⟨f⟩

/-- Coercion to apply a Setter as if it were its profunctor encoding. -/
instance : CoeFun (Setter s t a b)
              (fun _ => ∀ {P : Type → Type → Type} [Profunctor P], Strong P → P a b → P s t) where
  coe st := st.toSetter

/--
Affine traversals update at most one focus and require `Strong` and `Choice`.
-/
structure AffineTraversal (s t a b : Type) : Type 1 where
  toAffineTraversal : ∀ {P : Type → Type → Type} [Profunctor P], Strong P → Choice P → P a b → P s t

/-- Coercion to construct an AffineTraversal from its profunctor encoding. -/
instance : Coe (∀ {P : Type → Type → Type} [Profunctor P], Strong P → Choice P → P a b → P s t)
              (AffineTraversal s t a b) where
  coe f := ⟨f⟩

/-- Coercion to apply an AffineTraversal as if it were its profunctor encoding. -/
instance : CoeFun (AffineTraversal s t a b)
              (fun _ => ∀ {P : Type → Type → Type} [Profunctor P], Strong P → Choice P → P a b → P s t) where
  coe aff := aff.toAffineTraversal

abbrev Iso' (s a : Type) := Iso s s a a
abbrev Lens' (s : Type) (a : Type) := Lens s s a a
abbrev Prism' (s a : Type) := Prism s s a a
abbrev Traversal' (s a : Type) := Traversal s s a a
abbrev Fold' (s a : Type) := Fold s s a a
abbrev Setter' (s a : Type) := Setter s s a a
abbrev AffineTraversal' (s a : Type) := AffineTraversal s s a a

end Collimator
