import Batteries
import Collimator.Core.Profunctor
import Collimator.Core.Strong
import Collimator.Core.Choice

namespace Collimator.Core

open Batteries

universe u v

/--
`Wandering` profunctors support traversing structures through applicatives.
-/
class Wandering (P : Type u → Type u → Type v)
    [Profunctor P] [Strong P] [Choice P] where
  wander :
    ∀ {α β σ τ : Type u},
      (∀ {F : Type u → Type u} [Applicative F], (α → F β) → σ → F τ) →
      P α β → P σ τ

end Collimator.Core
