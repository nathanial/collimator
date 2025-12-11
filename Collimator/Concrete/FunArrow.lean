import Collimator.Core
import Batteries

namespace Collimator.Concrete

open Batteries
open Collimator.Core


/--
`FunArrow` wraps Lean's function profunctor with explicit structure.
-/
structure FunArrow (α : Type u) (β : Type u) where
  run : α → β

namespace FunArrow

variable {α : Type u} {β : Type u}

instance : CoeFun (FunArrow α β) (fun _ => α → β) where
  coe := FunArrow.run

@[simp] theorem run_mk (f : α → β) : FunArrow.run (FunArrow.mk f) = f := rfl
@[simp] theorem mk_apply (f : α → β) (a : α) : FunArrow.mk f a = f a := rfl

end FunArrow

instance instProfunctorFunArrow :
    Profunctor (fun α : Type u => fun β : Type u => FunArrow α β) where
  dimap f g p := FunArrow.mk (fun a' => g (p (f a')))

instance instStrongFunArrow :
    Strong (fun α : Type u => fun β : Type u => FunArrow α β) where
  first := fun p => FunArrow.mk (fun ac => (p ac.1, ac.2))
  second := fun p => FunArrow.mk (fun ca => (ca.1, p ca.2))

instance instChoiceFunArrow :
    Choice (fun α : Type u => fun β : Type u => FunArrow α β) where
  left :=
    fun p => FunArrow.mk <|
      fun
      | Sum.inl a => Sum.inl (p a)
      | Sum.inr c => Sum.inr c
  right :=
    fun p => FunArrow.mk <|
      fun
      | Sum.inl c => Sum.inl c
      | Sum.inr a => Sum.inr (p a)

instance instClosedFunArrow :
    Closed (fun α : Type u => fun β : Type u => FunArrow α β) where
  closed :=
    fun {α β γ} (p : FunArrow α β) =>
      FunArrow.mk (fun (k : γ → α) (x : γ) => p (k x))

instance instWanderingFunArrow :
    Wandering (fun α : Type u => fun β : Type u => FunArrow α β) where
  wander :=
    by
      intro α β σ τ walk p
      exact FunArrow.mk (fun s => walk (F := Id) (fun a => p a) s)

end Collimator.Concrete
