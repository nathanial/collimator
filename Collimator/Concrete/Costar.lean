import Collimator.Core
import Batteries

namespace Collimator.Concrete

open Collimator.Core
open Batteries


/--
`Costar F α β` is the profunctor `F α → β` for a functor `F`.
-/
structure Costar (F : Type u → Type u) (α : Type u) (β : Type u) where
  run : F α → β

namespace Costar

variable {F : Type u → Type u} {α β : Type u}

instance : CoeFun (Costar F α β) (fun _ => F α → β) where
  coe := Costar.run

@[simp] theorem run_mk (f : F α → β) : Costar.run (Costar.mk f) = f := rfl
@[simp] theorem mk_apply (f : F α → β) (fa : F α) : Costar.mk f fa = f fa := rfl

end Costar

instance instProfunctorCostar (F : Type u → Type u) [Functor F] :
    Profunctor (Costar F) where
  dimap f g p :=
    Costar.mk (fun fa' => g (p.run (Functor.map f fa')))

instance instClosedCostar (F : Type u → Type u) [Functor F] :
    Closed (Costar F) where
  closed :=
    fun {_ _ _} p =>
      Costar.mk (fun fga =>
        fun γVal => p.run (Functor.map (fun h => h γVal) fga))

end Collimator.Concrete
