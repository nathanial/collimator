import Collimator.Core
import Collimator.Control.Const

namespace Collimator.Concrete

open Collimator.Core

universe u₁ u₂ u₃

/--
`Forget R α β` keeps only an `R` value, ignoring its second type parameter.
-/
abbrev Forget (R : Type u₃) (α : Type u₁) (_β : Type u₂) := α → R

instance instProfunctorForget (R : Type u₃) :
    Profunctor (Forget (R := R)) where
  dimap pre _ p := fun a' => p (pre a')

instance instStrongForget (R : Type u₃) :
    Strong (Forget (R := R)) where
  first :=
    fun {α β _γ} (p : Forget R α β) (ac : α × _γ) => p ac.1
  second :=
    fun {α β _γ} (p : Forget R α β) (ca : _γ × α) => p ca.2

instance instChoiceForget (R : Type u₃) [Inhabited R] :
    Choice (Forget (R := R)) where
  left :=
    fun {α β _γ} (p : Forget R α β) =>
      fun
      | Sum.inl a => p a
      | Sum.inr (_c : _γ) => default
  right :=
    fun {α β _γ} (p : Forget R α β) =>
      fun
      | Sum.inl (_c : _γ) => default
      | Sum.inr a => p a

-- Provide One and Mul instances for List to enable Const applicative
instance instOneList {α : Type u₁} : One (List α) where
  one := []

instance instMulList {α : Type u₁} : Mul (List α) where
  mul := List.append

-- Wandering instance for Forget uses Const applicative (from mathlib)
-- Requires One and Mul for the applicative functor, and Inhabited for Choice
-- Note: wander requires all types in the same universe (F : Type u → Type u)
instance instWanderingForget (R : Type u₃) [Inhabited R] [One R] [Mul R] :
    Wandering (Forget (R := R)) where
  wander := by
    intro α β σ τ walk p s
    -- Since Const R β = R definitionally, walk will use Const R as the applicative
    exact walk (F := Collimator.Control.Const R) p s

end Collimator.Concrete
