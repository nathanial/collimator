import Collimator.Core.Profunctor
import Collimator.Optics.Types

namespace Collimator

open Collimator.Core

universe u v w

/--
Create an isomorphism from forward and backward maps.
-/
def iso {s t a b : Type _}
    (forward : s → a) (back : b → t) : Iso s t a b :=
  fun {P : Type u → Type v → Type w} [Profunctor P] =>
    Profunctor.dimap (P := P) forward back

/-- Identity optic. -/
def id {α : Type _} : Iso' α α :=
  iso (s := α) (t := α) (a := α) (b := α)
    (forward := fun x => x) (back := fun x => x)

end Collimator
