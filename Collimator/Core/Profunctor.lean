/-!
Core profunctor definitions for the Collimator optics library.
-/
namespace Collimator.Core

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

end Collimator.Core
