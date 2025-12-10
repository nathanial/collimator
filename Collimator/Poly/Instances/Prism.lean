import Collimator.Optics
import Collimator.Poly.Classes
import Collimator.Concrete.Forget
import Collimator.Concrete.Tagged
import Collimator.Concrete.FunArrow
import Collimator.Concrete.Star

/-!
# Polymorphic Instances for Prism

This module provides type class instances that allow Prism to work with the
polymorphic optics API.

## Instances Provided

- `HasPreview` - Optionally extract value via pattern match
- `HasReview` - Construct value via builder
- `HasOver` - Modify value via preview → f → review (if match succeeds)
- `HasSet` - Set value via review
- `HasTraverse` - Effectfully traverse via preview → f → map review

## Usage

```lean
import Collimator.Poly

open Collimator.Poly

def somePrism : Prism' (Option Int) Int :=
  prism some (fun opt => match opt with
    | some x => Sum.inr x
    | none => Sum.inl none)

-- Now you can use polymorphic operations!
let opt : Option Int := some 42
let value := preview somePrism opt              -- some 42
let opt' := review somePrism 100                -- some 100
let opt'' := over somePrism (· + 1) opt        -- some 43
```
-/

namespace Collimator.Poly

open Collimator
open Collimator.Concrete


/-! ## HasPreview Instance -/

/--
Prisms support preview: optionally extract a focused value.

For a prism `p : Prism' s a`, `preview p s` returns:
- `some a` if the pattern match succeeds
- `none` if it fails

Implementation: Uses the existing monomorphic `Collimator.preview` function.
-/
instance : HasPreview (fun (s a : Type) => Prism s s a a) where
  preview := Collimator.preview'

/-! ## HasReview Instance -/

/--
Prisms support review: construct a value from a part.

For a prism `p : Prism s t a b` and value `b`:
- `review p b` produces a value of type `t`

Implementation: Uses the existing monomorphic `Collimator.review` function.
-/
instance : HasReview Prism where
  review := Collimator.review'

/-! ## HasOver Instance -/

/--
Prisms support modification: apply a function if the pattern matches.

For a prism `p : Prism s t a b` and function `f : a → b`:
- `over p f s` applies `f` if the match succeeds, otherwise preserves structure

Implementation: Uses FunArrow profunctor to compose the transformation.
The Choice constraint ensures the function is lifted properly through the sum type.
-/
instance : HasOver Prism where
  over p f := (p (P := FunArrow) (FunArrow.mk f)).run

/-! ## HasSet Instance -/

/--
Prisms support setting: replace with a constant value.

For a prism `p : Prism s t a b` and value `b`:
- `set p b` constructs a new value using review

Implementation: Uses Tagged profunctor to extract the review direction.
Note: Unlike lenses, this ignores the original structure entirely.
-/
instance : HasSet Prism where
  set p b _s := p (P := fun α β => Tagged α β) b

/-! ## HasTraverse Instance -/

/--
Prisms support effectful traversal: apply an effectful function if the pattern matches.

For a prism `p : Prism s t a b`, applicative `F`, and function `f : a → F b`:
- `traverse p f s` applies `f` if the match succeeds, otherwise returns `pure s` unchanged

Implementation: Uses the Star profunctor which wraps `α → F β`.
The Choice instance for Star properly handles the Sum type:
- When pattern matches: applies the effectful function
- When pattern fails: returns the "failure" value wrapped in pure

This leverages the profunctor encoding to handle polymorphic prisms correctly.
-/
instance : HasTraverse Prism where
  traverse {_s _t _a _b F} [Applicative F] p f s :=
    let star : Star F _a _b := Concrete.Star.mk f
    let result := p (P := Star F) star
    result.run s

end Collimator.Poly
