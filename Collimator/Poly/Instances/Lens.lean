import Collimator.Optics.Lens
import Collimator.Poly.Classes
import Collimator.Concrete.Forget
import Collimator.Concrete.FunArrow

/-!
# Polymorphic Instances for Lens

This module provides type class instances that allow Lens to work with the
polymorphic optics API.

## Instances Provided

- `HasView` - Extract value via getter
- `HasOver` - Modify value via getter → f → setter
- `HasSet` - Set value via setter
- `HasPreview` - Always succeeds with `some (view ...)`
- `HasTraverse` - Effectfully traverse via view → f → map set

## Usage

```lean
import Collimator.Poly

open Collimator.Poly

def fstLens : Lens' (Int × String) Int :=
  lens (fun p => p.1) (fun p v => (v, p.2))

-- Now you can use polymorphic operations!
let pair : (Int × String) := (42, "hello")
let value := view fstLens pair                    -- 42
let pair' := set fstLens 100 pair                 -- (100, "hello")
let pair'' := over fstLens (· + 1) pair          -- (43, "hello")
```
-/

namespace Collimator.Poly

open Collimator
open Collimator.Concrete


/-! ## HasView Instance -/

/--
Lenses support viewing: extract the focused value using the getter.

For a lens `l : Lens' s a`, `view l s` extracts the `a` value from `s`.

Implementation: Uses the existing monomorphic `Collimator.view` function.
-/
@[instance 10001] -- Higher priority than Iso (10000) to prefer Lens when argument is a Lens
instance : HasView (fun (s a : Type) => Lens s s a a) where
  view := Collimator.view'

/-! ## HasOver Instance -/

/--
Lenses support modification: apply a function to the focused value.

For a lens `l : Lens s t a b` and function `f : a → b`:
- `over l f` produces a function `s → t`

Implementation: Uses the existing monomorphic `Collimator.over` function.
-/
instance : HasOver Lens where
  over := Collimator.over'

/-! ## HasSet Instance -/

/--
Lenses support setting: replace the focused value.

For a lens `l : Lens s t a b` and value `b`:
- `set l b` produces a function `s → t`

Implementation: Uses the existing monomorphic `Collimator.set` function.
-/
instance : HasSet Lens where
  set := Collimator.set'

/-! ## HasPreview Instance -/

/--
Lenses support preview: always succeeds because lenses are total.

For a lens `l : Lens' s a`:
- `preview l s` = `some (view l s)`

Unlike prisms which may fail, lenses always succeed.
-/
instance : HasPreview (fun (s a : Type) => Lens s s a a) where
  preview l s := some (Collimator.view' l s)

/-! ## HasTraverse Instance -/

/--
Lenses support effectful traversal: apply an effectful function to the focus.

For a lens `l : Lens s t a b`, applicative `F`, and function `f : a → F b`:
- `traverse l f s` applies f to the focused value

Implementation: First view to get `a`, apply `f` to get `F b`, then map set over the result.
This follows the pattern:
1. Extract focused value: s → a
2. Apply effectful function: a → F b
3. Map set over the effect: F b → F t
-/
instance : HasTraverse Lens where
  traverse {_s _t a _b F} [Applicative F] l f s :=
    -- Use Forget to extract the focused value
    let forget : Forget a a a := fun y => y
    let aval := (l.toLens (P := fun α β => Forget a α β) inferInstance forget) s
    let fb := f aval
    -- Map over the effect, using FunArrow to set the new value
    Functor.map (fun bval =>
      let arrow := FunArrow.mk (fun _ => bval)
      (l.toLens (P := fun α β => FunArrow α β) inferInstance arrow) s
    ) fb

end Collimator.Poly
