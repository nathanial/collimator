import Collimator.Optics
import Collimator.Combinators

namespace Collimator.Instances.Prod

open Collimator
open Collimator.Combinators


/-- Lens focusing the first component of a pair. -/
@[inline] def first {α β γ : Type} :
    Lens (α × β) (γ × β) α γ :=
  _1

/-- Lens focusing the second component of a pair. -/
@[inline] def second {α β γ : Type} :
    Lens (α × β) (α × γ) β γ :=
  _2

/-- Lens focusing the first element of a triple represented as nested pairs. -/
@[inline] def firstOfTriple {α β γ δ : Type} :
    Lens ((α × β) × γ) ((δ × β) × γ) α δ :=
  _1 ∘ _1

/-- Lens focusing the middle element of a triple represented as nested pairs. -/
@[inline] def secondOfTriple {α β γ δ : Type} :
    Lens ((α × β) × γ) ((α × δ) × γ) β δ :=
  _1 ∘ _2

/-- Lens focusing the final element of a triple represented as nested pairs. -/
@[inline] def thirdOfTriple {α β γ δ : Type} :
    Lens ((α × β) × γ) ((α × β) × δ) γ δ :=
  _2

end Collimator.Instances.Prod
