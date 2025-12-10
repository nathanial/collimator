import Collimator.Optics.Iso
import Collimator.Theorems.IsoLaws
import Collimator.Poly.Classes
import Collimator.Concrete.Forget
import Collimator.Concrete.Tagged
import Collimator.Concrete.FunArrow

/-!
# Polymorphic Instances for Iso

This module provides type class instances that allow Iso to work with the
polymorphic optics API.

## Instances Provided

- `HasView` - Extract value via forward direction
- `HasOver` - Modify value via forward → f → backward
- `HasSet` - Set value via backward direction
- `HasPreview` - Always succeeds with `some (view ...)`
- `HasReview` - Construct via backward direction
- `HasTraverse` - Effectfully traverse via forward → f → map backward

## Usage

```lean
import Collimator.Poly

open Collimator.Poly

def complexIso : Iso' Complex (Float × Float) :=
  iso (fun c => (c.real, c.imag)) (fun (r, i) => ⟨r, i⟩)

-- Now you can use polymorphic operations!
let c : Complex := ⟨3.0, 4.0⟩
let pair := view complexIso c                    -- (3.0, 4.0)
let c' := set complexIso (5.0, 12.0) c          -- Complex.mk 5.0 12.0
let c'' := over complexIso (fun (r, i) => (r*2, i*2)) c
```
-/

namespace Collimator.Poly

open Collimator
open Collimator.Theorems
open Collimator.Concrete


/-! ## HasView Instance -/

/--
Isos support viewing: extract the focused value using the forward direction.

For an iso `i : Iso' s a`, `view i s` extracts the `a` value from `s`.

Implementation: Uses the Forget profunctor to extract the forward direction.
-/
@[instance 10000] -- Higher priority than Lens instance (default is 1000)
instance : HasView (fun (s a : Type) => Iso s s a a) where
  view {_s a} i x :=
    let forget : Forget a a a := fun y => y
    let result := i.toIso (P := fun α β => Forget a α β) forget
    result x

/-! ## HasOver Instance -/

/--
Isos support modification: apply a function by going forward, transforming, then backward.

For an iso `i : Iso s t a b` and function `f : a → b`:
- `over i f` produces a function `s → t`

Implementation: Uses the FunArrow profunctor to compose the iso with the function.
This follows the pattern: s → a (forward) → b (transform) → t (backward).
-/
@[instance 10000] -- Higher priority than Lens/Prism instances (default is 1000)
instance : HasOver Iso where
  over i f := (i.toIso (P := FunArrow) (FunArrow.mk f)).run

/-! ## HasSet Instance -/

/--
Isos support setting: replace the value using the backward direction.

For an iso `i : Iso s t a b` and value `b`:
- `set i b` produces a function `s → t` that ignores its input

Implementation: Uses the Tagged profunctor to extract the backward direction.
Note: The original `s` value is ignored because an iso is invertible.
-/
@[instance 10000] -- Higher priority than Lens/Prism instances (default is 1000)
instance : HasSet Iso where
  set i b _s := i.toIso (P := fun α β => Tagged α β) b

/-! ## HasPreview Instance -/

/--
Isos support preview: always succeeds because isos are total.

For an iso `i : Iso' s a`:
- `preview i s` = `some (view i s)`

Unlike prisms or affine traversals which may fail, isos always succeed.
-/
@[instance 10000] -- Higher priority than Lens/Prism instances (default is 1000)
instance : HasPreview (fun (s a : Type) => Iso s s a a) where
  preview {_s a} i x :=
    let forget : Forget a a a := fun y => y
    let result := i.toIso (P := fun α β => Forget a α β) forget
    some (result x)

/-! ## HasReview Instance -/

/--
Isos support review: construct the whole from a part using the backward direction.

For an iso `i : Iso s t a b` and value `b`:
- `review i b` produces a value of type `t`

Implementation: Uses the Tagged profunctor to extract the backward direction.
This is identical to `set` for isos, but semantically represents construction
rather than modification.
-/
@[instance 10000] -- Higher priority than Prism instance (default is 1000)
instance : HasReview Iso where
  review i b := i.toIso (P := fun α β => Tagged α β) b

/-! ## HasTraverse Instance -/

/--
Isos support effectful traversal: apply an effectful function through the iso.

For an iso `i : Iso s t a b`, applicative `F`, and function `f : a → F b`:
- `traverse i f s` applies f through the iso

Implementation: First view to get `a`, apply `f` to get `F b`, then map review over the result.
This follows the pattern:
1. Go forward: s → a
2. Apply effectful function: a → F b
3. Map backward over the effect: F b → F t
-/
@[instance 10000] -- Higher priority than Lens/Prism instances (default is 1000)
instance : HasTraverse Iso where
  traverse {_s _t a _b F} [Applicative F] i f x :=
    let forget : Forget a a a := fun y => y
    let aval := (i.toIso (P := fun α β => Forget a α β) forget) x
    let fb := f aval
    Functor.map (fun bval => i.toIso (P := fun α β => Tagged α β) bval) fb

end Collimator.Poly
