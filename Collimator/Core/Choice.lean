import Collimator.Core.Profunctor

namespace Collimator.Core

universe u v

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

end Collimator.Core
