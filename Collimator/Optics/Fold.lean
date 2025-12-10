import Batteries
import Collimator.Optics.Types
import Collimator.Optics.Lens
import Collimator.Optics.Affine
import Collimator.Optics.Traversal
import Collimator.Concrete.Forget
import Collimator.Core.Wandering

namespace Collimator

open Batteries
open Collimator.Core
open Collimator.Concrete


namespace Fold

/-- Every lens gives a fold that observes its focus. -/
def ofLens {s t a b : Type _}
    (l : Lens s t a b) : Collimator.Fold s t a b :=
  ⟨fun {P} [Profunctor P] hStrong _ pab => l.toLens (P := P) hStrong pab⟩

/-- Every affine traversal can be used as a fold. -/
def ofAffine {s t a b : Type _}
    (aff : Collimator.AffineTraversal s t a b) : Collimator.Fold s t a b :=
  ⟨fun {P} [Profunctor P] hStrong hChoice pab => aff.toAffineTraversal (P := P) hStrong hChoice pab⟩

/-- Collect all focuses of a fold into a list. -/
def toList {s a : Type _} [Inhabited (List a)]
    (fld : Fold' s a) (s₀ : s) : List a :=
  let forget : Forget (List a) a a := fun x => [x]
  let lifted :=
    fld.toFold (P := fun α β => Forget (List a) α β) inferInstance inferInstance forget
  lifted s₀

/-- Collect all focuses of a traversal into a list using Forget's Wandering instance. -/
def toListTraversal {s a : Type _} [Inhabited (List a)]
    (tr : Traversal' s a) (s₀ : s) : List a :=
  let forget : Forget (List a) a a := fun x => [x]
  let lifted := tr.toTraversal (P := Forget (List a)) inferInstance forget
  lifted s₀

/-- Compose a lens with a fold to focus deeper. -/
@[inline] def composeLensFold
    {s t a b u v : Type _}
    (outer : Lens s t a b) (inner : Collimator.Fold a b u v) :
    Collimator.Fold s t u v :=
  fun {P} [Profunctor P] hStrong hChoice puv =>
    outer.toLens (P := P) hStrong (inner.toFold (P := P) hStrong hChoice puv)

/-- Compose two folds to read through nested structures. -/
@[inline] def composeFold
    {s t a b u v : Type _}
    (outer : Collimator.Fold s t a b) (inner : Collimator.Fold a b u v) :
    Collimator.Fold s t u v :=
  fun {P} [Profunctor P] hStrong hChoice puv =>
    outer.toFold (P := P) hStrong hChoice (inner.toFold (P := P) hStrong hChoice puv)

scoped infixr:80 " ∘ₗf " => composeLensFold
scoped infixr:80 " ∘f " => composeFold

end Fold

end Collimator
