import Collimator.Core.Profunctor

namespace Collimator.Core

universe u₁ u₂ u₃ u₄

/--
Lawful profunctors satisfy identity and composition laws for `dimap`.
-/
class LawfulProfunctor (P : Type u₁ → Type u₂ → Type u₃) [Profunctor P] where
  dimap_id : ∀ {α β},
    Profunctor.dimap (P := P) (fun x : α => x) (fun x : β => x) = id
  dimap_comp : ∀ {α α' α'' β β' β''}
      (f : α' → α) (f' : α'' → α')
      (g : β → β') (g' : β' → β''),
    Profunctor.dimap (P := P) (f ∘ f') (g' ∘ g)
      = Profunctor.dimap (P := P) f' g' ∘ Profunctor.dimap (P := P) f g

variable {P : Type u₁ → Type u₂ → Type u₃}

@[simp] theorem dimap_id (p : P α β) [Profunctor P] [LawfulProfunctor P] :
    Profunctor.dimap (P := P) (fun x : α => x) (fun x : β => x) p = p :=
  by
    have := LawfulProfunctor.dimap_id (P := P) (α := α) (β := β)
    exact congrArg (fun f => f p) this

@[simp] theorem lmap_id {P} [Profunctor P] [LawfulProfunctor P]
    (p : P α β) : lmap (P := P) (fun x : α => x) p = p :=
  by
    simp [lmap, dimap_id]

@[simp] theorem rmap_id {P} [Profunctor P] [LawfulProfunctor P]
    (p : P α β) : rmap (P := P) (fun x : β => x) p = p :=
  by
    simp [rmap, dimap_id]

@[simp] theorem dimap_comp
    [Profunctor P] [LawfulProfunctor P]
    (f : α' → α) (f' : α'' → α')
    (g : β → β') (g' : β' → β'') (p : P α β) :
    Profunctor.dimap (P := P) (f ∘ f') (g' ∘ g) p
      = Profunctor.dimap (P := P) f' g'
          (Profunctor.dimap (P := P) f g p) :=
  by
    have := LawfulProfunctor.dimap_comp (P := P)
      (α := α) (α' := α') (α'' := α'')
      (β := β) (β' := β') (β'' := β'') f f' g g'
    exact congrArg (fun h => h p) this

/--
The function profunctor is lawful.
-/
instance instLawfulProfunctorArrow :
    LawfulProfunctor (fun α : Type u₁ => fun β : Type u₂ => α → β) where
  dimap_id :=
    by
      intro α β
      funext p a
      rfl
  dimap_comp :=
    by
      intro α α' α'' β β' β'' f f' g g'
      funext p a
      rfl

/--
The constant profunctor is lawful.
-/
instance instLawfulProfunctorConst (R : Type u₄) :
    LawfulProfunctor (Const (R := R)) where
  dimap_id :=
    by
      intro α β
      funext p
      rfl
  dimap_comp :=
    by
      intro α α' α'' β β' β'' f f' g g'
      funext p
      rfl

/--
Kleisli profunctors are lawful when the underlying functor is lawful.
-/
instance instLawfulProfunctorKleisli (m : Type u₂ → Type u₃)
    [Functor m] [LawfulFunctor m] :
    LawfulProfunctor (Kleisli m) where
  dimap_id :=
    by
      intro α β
      funext p a
      exact LawfulFunctor.id_map (f := m) (x := p a)
  dimap_comp :=
    by
      intro α α' α'' β β' β'' f f' g g'
      funext p a
      exact
        LawfulFunctor.comp_map (f := m)
          (g := g) (h := g') (x := p (f (f' a)))

end Collimator.Core
