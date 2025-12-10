import Collimator.Optics.Types
import Collimator.Optics.Traversal

namespace Collimator.Combinators

open Collimator
open Collimator.Traversal

universe u

/--
Restrict a traversal to focuses that satisfy a predicate. The traversal is
monomorphic because the predicate must be evaluated on both the input and the
output type.
-/
def filtered {s : Type u} {a : Type u}
    (tr : Traversal' s a) (pred : a → Bool) : Traversal' s a :=
  Collimator.traversal
    (fun {F : Type u → Type u} [Applicative F]
      (f : a → F a) (s₀ : s) =>
        Traversal.traverse' (tr := tr)
          (fun a => if pred a then f a else pure a)
          s₀)

end Collimator.Combinators
