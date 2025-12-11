import Collimator.Core
import Batteries

namespace Collimator.Concrete

open Collimator.Core
open Batteries


/--
`Star F α β` is the profunctor `α → F β` for some applicative functor `F`.
-/
structure Star (F : Type u → Type u) (α : Type u) (β : Type u) where
  run : α → F β

namespace Star

variable {F : Type u → Type u} {α β : Type u}

instance : CoeFun (Star F α β) (fun _ => α → F β) where
  coe := Star.run

@[simp] theorem run_mk (f : α → F β) : Star.run (Star.mk f) = f := rfl
@[simp] theorem mk_apply (f : α → F β) (a : α) : Star.mk f a = f a := rfl

end Star

instance instProfunctorStar (F : Type u → Type u) [Functor F] :
    Profunctor (Star F) where
  dimap f g p :=
    Star.mk (fun a' => Functor.map g (p.run (f a')))

instance instStrongStar (F : Type u → Type u) [Applicative F] :
    Strong (Star F) where
  first :=
    fun {α β _γ} (p : Star F α β) =>
      Star.mk (fun (ac : α × _γ) =>
        Functor.map (fun b => (b, ac.2)) (p.run ac.1))
  second :=
    fun {α β _γ} (p : Star F α β) =>
      Star.mk (fun (ca : _γ × α) =>
        Functor.map (fun b => (ca.1, b)) (p.run ca.2))

instance instChoiceStar (F : Type u → Type u) [Applicative F] :
    Choice (Star F) where
  left :=
    fun {α β _γ} (p : Star F α β) =>
      Star.mk <|
        fun
        | Sum.inl a => Functor.map Sum.inl (p.run a)
        | Sum.inr (c : _γ) => pure (Sum.inr c)
  right :=
    fun {α β _γ} (p : Star F α β) =>
      Star.mk <|
        fun
        | Sum.inl (c : _γ) => pure (Sum.inl c)
        | Sum.inr a => Functor.map Sum.inr (p.run a)

instance instWanderingStar (F : Type u → Type u) [Applicative F] :
    Wandering (Star F) where
  wander :=
    by
      intro α β σ τ walk p
      exact Star.mk (fun s => walk (F := F) p.run s)

end Collimator.Concrete
