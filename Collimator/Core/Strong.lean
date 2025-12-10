import Collimator.Core.Profunctor

namespace Collimator.Core

universe u v

/--
Strong profunctors can manipulate products.
-/
class Strong (P : Type u → Type u → Type v) [Profunctor P] where
  first  : ∀ {α β γ : Type u}, P α β → P (α × γ) (β × γ)
  second : ∀ {α β γ : Type u}, P α β → P (γ × α) (γ × β)

instance instStrongArrow : Strong (fun α β : Type u => α → β) where
  first := fun _ab (a, c) => (_ab a, c)
  second := fun _ab (c, a) => (c, _ab a)

end Collimator.Core
