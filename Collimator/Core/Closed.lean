import Collimator.Core.Profunctor

namespace Collimator.Core

universe u v

/--
Closed profunctors can operate on function spaces.
-/
class Closed (P : Type u → Type u → Type v) [Profunctor P] where
  closed : ∀ {α β γ : Type u}, P α β → P (γ → α) (γ → β)

instance instClosedArrow : Closed (fun α β : Type u => α → β) where
  closed := fun {α β γ} (p : α → β) =>
    fun (k : γ → α) (x : γ) => p (k x)

end Collimator.Core
