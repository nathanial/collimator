import Collimator.Optics.Types
import Collimator.Optics.Prism
import Collimator.Optics.Lens
import Collimator.Concrete.FunArrow
import Collimator.Concrete.Forget

namespace Collimator

open Collimator.Core
open Collimator.Concrete

universe u

namespace AffineTraversalOps

/-- Modify the target of an affine traversal. -/
def over {s t a b : Type _}
    (aff : Collimator.AffineTraversal s t a b) (f : a → b) : s → t :=
  let arrow := FunArrow.mk (α := a) (β := b) f
  let transformed := aff.toAffineTraversal (P := fun α β => FunArrow α β) inferInstance inferInstance arrow
  fun s => transformed s

/-- Set the target of an affine traversal to a constant value. -/
def set {s t a b : Type _}
    (aff : Collimator.AffineTraversal s t a b) (value : b) : s → t :=
  over aff (fun _ => value)

/-- Attempt to preview the focused value of an affine traversal. -/
def preview' {s a : Type _}
    (aff : Collimator.AffineTraversal' s a) (s₀ : s) : Option a :=
  let forget := fun a : a => some a
  let transformed :=
    aff.toAffineTraversal (P := fun α β => Forget (Option a) α β) inferInstance inferInstance forget
  transformed s₀

/-- Every prism is an affine traversal. -/
def ofPrism {s t a b : Type _}
    (p : Prism s t a b) : Collimator.AffineTraversal s t a b :=
  ⟨fun {P} [Profunctor P] _hStrong hChoice pab =>
    p.toPrism (P := P) hChoice pab⟩

/-- Every lens yields an affine traversal focusing exactly one target. -/
def ofLens {s t a b : Type _}
    (l : Lens s t a b) : Collimator.AffineTraversal s t a b :=
  ⟨fun {P} [Profunctor P] hStrong _ pab =>
    l.toLens (P := P) hStrong pab⟩

end AffineTraversalOps

end Collimator
