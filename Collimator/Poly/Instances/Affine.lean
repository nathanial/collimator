import Collimator.Optics
import Collimator.Poly.Classes
import Collimator.Concrete.Star

/-!
# Polymorphic Instances for AffineTraversal

This module provides type class instances that allow AffineTraversal to work with the
polymorphic optics API.

## Instances Provided

- `HasPreview` - Optionally extract value (may fail if no focus)
- `HasOver` - Modify focused value if present
- `HasSet` - Set focused value if present
- `HasTraverse` - Effectfully traverse the focus if present

## Usage

```lean
import Collimator.Poly

open Collimator.Poly

-- AffineTraversal focuses at most one element
def maybeHead : AffineTraversal' (List Int) Int := ...

-- Now you can use polymorphic operations!
let list : List Int := [1, 2, 3]
let value := preview maybeHead list             -- some 1
let list' := over maybeHead (· + 1) list        -- [2, 2, 3]
let list'' := set maybeHead 0 list              -- [0, 2, 3]
```
-/

namespace Collimator.Poly

open Collimator
open Collimator.Concrete


/-! ## HasPreview Instance -/

/--
AffineTraversals support preview: optionally extract the focused value.

For an affine traversal `aff : AffineTraversal' s a`, `preview aff s` returns:
- `some a` if the focus exists
- `none` if there is no focus

Implementation: Uses the existing monomorphic `Collimator.AffineTraversalOps.preview` function.
-/
instance : HasPreview (fun (s a : Type) => AffineTraversal s s a a) where
  preview := AffineTraversalOps.preview'

/-! ## HasOver Instance -/

/--
AffineTraversals support modification: apply a function to the focus if present.

For an affine traversal `aff : AffineTraversal s t a b` and function `f : a → b`:
- `over aff f s` applies `f` if the focus exists, otherwise preserves structure

Implementation: Uses the existing monomorphic `Collimator.AffineTraversalOps.over` function.
-/
instance : HasOver AffineTraversal where
  over := AffineTraversalOps.over

/-! ## HasSet Instance -/

/--
AffineTraversals support setting: replace the focused value if present.

For an affine traversal `aff : AffineTraversal s t a b` and value `b`:
- `set aff b s` replaces the focus with `b` if it exists, otherwise preserves structure

Implementation: Uses the existing monomorphic `Collimator.AffineTraversalOps.set` function.
-/
instance : HasSet AffineTraversal where
  set := AffineTraversalOps.set

/-! ## HasTraverse Instance -/

/--
AffineTraversals support effectful traversal: apply an effectful function to the focus if present.

For an affine traversal `aff : AffineTraversal s t a b`, applicative `F`, and function `f : a → F b`:
- `traverse aff f s` applies `f` if the focus exists, otherwise returns `pure s` unchanged

Implementation: Uses the Star profunctor which wraps `α → F β`.
The Strong and Choice instances for Star handle the affine structure:
- When focus exists: applies the effectful function
- When focus doesn't exist: returns the structure wrapped in pure
-/
instance : HasTraverse AffineTraversal where
  traverse {_s _t _a _b F} [Applicative F] aff f s :=
    let star : Star F _a _b := Concrete.Star.mk f
    let result := aff (P := Star F) star
    result s

end Collimator.Poly
