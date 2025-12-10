import Collimator.Core.Profunctor
import Collimator.Core.Choice
import Collimator.Optics.Types
import Collimator.Concrete.Forget
import Collimator.Concrete.Tagged

namespace Collimator

open Collimator.Core
open Collimator.Concrete

universe u

/--
Construct a prism from a builder and a matcher.
-/
def prism {s t a b : Type _}
    (build : b → t) (split : s → Sum t a) : Prism s t a b :=
  fun {P} [Profunctor P] hChoice pab =>
    let _ : Choice P := hChoice
    let right := Choice.right (P := P) (γ := t) pab
    let post : Sum t b → t :=
      Sum.elim (fun t' => t') (fun b' => build b')
    Profunctor.dimap (P := P) split post right

/-- Attempt to extract a focused value with a prism. -/
def preview' {s a : Type _}
    (p : Prism' s a) (x : s) : Option a :=
  let forget : Forget (Option a) a a := fun a => some a
  let result := p.toPrism (P := fun α β => Forget (Option a) α β) inferInstance forget
  result x

/-- Inject a value through a prism. -/
def review' {s t a b : Type _}
    (p : Prism s t a b) (b₀ : b) : t :=
  p.toPrism (P := fun α β => Tagged α β) inferInstance b₀

end Collimator
