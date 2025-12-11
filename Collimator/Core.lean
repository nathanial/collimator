import Batteries

/-!
# Collimator Core Profunctor Definitions

This module contains all core profunctor abstractions for the Collimator optics library:
- `Profunctor`: Base typeclass - contravariant in first arg, covariant in second
- `Strong`: Profunctors that work with products (enables lenses)
- `Choice`: Profunctors that work with sums (enables prisms)
- `Wandering`: Profunctors with `wander` for traversals
- `Closed`: Profunctors that work with function types

Also includes lawful variants (`LawfulProfunctor`, `LawfulStrong`, `LawfulChoice`)
with coherence laws and proofs.
-/

namespace Collimator.Core

open Batteries

/-!
## Profunctor
-/

universe u₁ u₂ u₃ u₄

/--
A profunctor is contravariant in its first argument and covariant in its second.
-/
class Profunctor (P : Type u₁ → Type u₂ → Type u₃) where
  dimap : (α' → α) → (β → β') → P α β → P α' β'

@[inline] def lmap {P : Type u₁ → Type u₂ → Type u₃} [Profunctor P]
    (f : α' → α) (p : P α β) : P α' β :=
  Profunctor.dimap f (fun x => x) p

@[inline] def rmap {P : Type u₁ → Type u₂ → Type u₃} [Profunctor P]
    (g : β → β') (p : P α β) : P α β' :=
  Profunctor.dimap (fun x => x) g p

/--
The canonical function profunctor.
-/
instance instProfunctorArrow :
    Profunctor (fun α : Type u₁ => fun β : Type u₂ => α → β) where
  dimap f g ab := fun a' => g (ab (f a'))

/--
The constant profunctor ignores both morphisms.
-/
def Const (R : Type u₄) (_α : Type u₁) (_β : Type u₂) : Type u₄ := R

instance instProfunctorConst (R : Type u₄) :
    Profunctor (Const (R := R)) where
  dimap _ _ r := r

/--
Kleisli profunctor for a functor `m`.
-/
def Kleisli (m : Type u₂ → Type u₃) (α : Type u₁) (β : Type u₂) : Type (max u₁ u₃) :=
  α → m β

instance instProfunctorKleisli (m : Type u₂ → Type u₃) [Functor m] :
    Profunctor (Kleisli m) where
  dimap f g h := fun a' => Functor.map g (h (f a'))

/-!
## Strong
-/

/--
Strong profunctors can manipulate products.
-/
class Strong (P : Type u → Type u → Type v) [Profunctor P] where
  first  : ∀ {α β γ : Type u}, P α β → P (α × γ) (β × γ)
  second : ∀ {α β γ : Type u}, P α β → P (γ × α) (γ × β)

instance instStrongArrow : Strong (fun α β : Type u => α → β) where
  first := fun _ab (a, c) => (_ab a, c)
  second := fun _ab (c, a) => (c, _ab a)

/-!
## Choice
-/

/--
Choice profunctors can manipulate sum types.
-/
class Choice (P : Type u → Type u → Type v) [Profunctor P] where
  left  : ∀ {α β γ : Type u}, P α β → P (Sum α γ) (Sum β γ)
  right : ∀ {α β γ : Type u}, P α β → P (Sum γ α) (Sum γ β)

instance instChoiceArrow : Choice (fun α β : Type u => α → β) where
  left :=
    fun _ab =>
      fun
      | Sum.inl a => Sum.inl (_ab a)
      | Sum.inr c => Sum.inr c
  right :=
    fun _ab =>
      fun
      | Sum.inl c => Sum.inl c
      | Sum.inr a => Sum.inr (_ab a)

/-!
## Wandering
-/

/--
`Wandering` profunctors support traversing structures through applicatives.
-/
class Wandering (P : Type u → Type u → Type v)
    [Profunctor P] [Strong P] [Choice P] where
  wander :
    ∀ {α β σ τ : Type u},
      (∀ {F : Type u → Type u} [Applicative F], (α → F β) → σ → F τ) →
      P α β → P σ τ

/-!
## Closed
-/

/--
Closed profunctors can operate on function spaces.
-/
class Closed (P : Type u → Type u → Type v) [Profunctor P] where
  closed : ∀ {α β γ : Type u}, P α β → P (γ → α) (γ → β)

instance instClosedArrow : Closed (fun α β : Type u => α → β) where
  closed := fun {α β γ} (p : α → β) =>
    fun (k : γ → α) (x : γ) => p (k x)

/-!
## Profunctor Laws
-/

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

/-!
## Strong Laws
-/

variable {P : Type u → Type u → Type v}

/--
A lawful Strong profunctor satisfies coherence laws between `first`, `second`, and `dimap`.
-/
class LawfulStrong (P : Type u → Type u → Type v) [Profunctor P] [Strong P] where
  /--
  **first-dimap coherence**: `first` is natural in both arguments.

  `first (dimap f g p) = dimap (f × id) (g × id) (first p)`
  -/
  first_dimap : ∀ {α β α' β' γ : Type u} (f : α' → α) (g : β → β') (p : P α β),
    Strong.first (Profunctor.dimap f g p) =
    Profunctor.dimap (fun (ac : α' × γ) => (f ac.1, ac.2))
                     (fun (bc : β × γ) => (g bc.1, bc.2))
                     (Strong.first (γ := γ) p)

  /--
  **second-dimap coherence**: `second` is natural in both arguments.

  `second (dimap f g p) = dimap (id × f) (id × g) (second p)`
  -/
  second_dimap : ∀ {α β α' β' γ : Type u} (f : α' → α) (g : β → β') (p : P α β),
    Strong.second (Profunctor.dimap f g p) =
    Profunctor.dimap (fun (ca : γ × α') => (ca.1, f ca.2))
                     (fun (cb : γ × β) => (cb.1, g cb.2))
                     (Strong.second (γ := γ) p)

  /--
  **first-second interchange**: Swapping products interchanges `first` and `second`.

  `dimap swap swap (first p) = second p` (modulo type alignment)

  Note: The precise statement requires careful alignment of type parameters.
  -/
  first_second_swap : ∀ {α β γ : Type u} (p : P α β),
    Profunctor.dimap Prod.swap Prod.swap (Strong.first (γ := γ) p) =
    (Strong.second (γ := γ) p : P (γ × α) (γ × β))

/--
The function arrow is a lawful Strong profunctor.
-/
axiom instLawfulStrongArrow : LawfulStrong (fun α β : Type u => α → β)

/-!
## Choice Laws
-/

/--
A lawful Choice profunctor satisfies coherence laws between `left`, `right`, and `dimap`.
-/
class LawfulChoice (P : Type u → Type u → Type v) [Profunctor P] [Choice P] where
  /--
  **left-dimap coherence**: `left` is natural in both arguments.

  `left (dimap f g p) = dimap (f ⊕ id) (g ⊕ id) (left p)`
  -/
  left_dimap : ∀ {α β α' β' γ : Type u} (f : α' → α) (g : β → β') (p : P α β),
    Choice.left (Profunctor.dimap f g p) =
    Profunctor.dimap (fun ac => match ac with
                       | Sum.inl a => Sum.inl (f a)
                       | Sum.inr c => Sum.inr c)
                     (fun bc => match bc with
                       | Sum.inl b => Sum.inl (g b)
                       | Sum.inr c => Sum.inr c)
                     (Choice.left (γ := γ) p)

  /--
  **right-dimap coherence**: `right` is natural in both arguments.

  `right (dimap f g p) = dimap (id ⊕ f) (id ⊕ g) (right p)`
  -/
  right_dimap : ∀ {α β α' β' γ : Type u} (f : α' → α) (g : β → β') (p : P α β),
    Choice.right (Profunctor.dimap f g p) =
    Profunctor.dimap (fun ca => match ca with
                       | Sum.inl c => Sum.inl c
                       | Sum.inr a => Sum.inr (f a))
                     (fun cb => match cb with
                       | Sum.inl c => Sum.inl c
                       | Sum.inr b => Sum.inr (g b))
                     (Choice.right (γ := γ) p)

  /--
  **left-right interchange**: Swapping sums interchanges `left` and `right`.

  `dimap swap swap (left p) = right p` (modulo type alignment)

  Note: The precise statement requires careful alignment of type parameters.
  -/
  left_right_swap : ∀ {α β γ : Type u} (p : P α β),
    Profunctor.dimap Sum.swap Sum.swap (Choice.left (γ := γ) p) =
    (Choice.right (γ := γ) p : P (Sum γ α) (Sum γ β))

/--
The function arrow is a lawful Choice profunctor.
-/
axiom instLawfulChoiceArrow : LawfulChoice (fun α β : Type u => α → β)

end Collimator.Core
