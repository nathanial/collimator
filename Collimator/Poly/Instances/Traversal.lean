import Collimator.Optics
import Collimator.Poly.Classes
import Collimator.Concrete.Star

/-!
# Polymorphic Instances for Traversal

This module provides type class instances that allow Traversal to work with the
polymorphic optics API.

## Instances Provided

- `HasOver` - Modify each focus via traversal
- `HasSet` - Set each focus to a constant value
- `HasTraverse` - Effectfully traverse each focus

## Usage

```lean
import Collimator.Poly

open Collimator.Poly

def listTraversal : Traversal' (List Int) Int :=
  Traversal.eachList

-- Now you can use polymorphic operations!
let list : List Int := [1, 2, 3]
let list' := over listTraversal (· + 1) list        -- [2, 3, 4]
let list'' := set listTraversal 0 list              -- [0, 0, 0]
```
-/

namespace Collimator.Poly

open Collimator
open Collimator.Concrete


/-! ## HasOver Instance -/

/--
Traversals support modification: apply a function to each focused value.

For a traversal `t : Traversal s t a b` and function `f : a → b`:
- `over t f` applies `f` to each focus in the structure

Implementation: Uses the existing monomorphic `Collimator.Traversal.over` function.
-/
instance : HasOver Traversal where
  over := Traversal.over'

/-! ## HasSet Instance -/

/--
Traversals support setting: replace each focused value with a constant.

For a traversal `t : Traversal s t a b` and value `b`:
- `set t b` replaces each focus with `b`

Implementation: Uses over with a constant function.
-/
instance : HasSet Traversal where
  set t b := Traversal.over' t (fun _ => b)

/-! ## HasTraverse Instance -/

/--
Traversals support effectful traversal: apply an effectful function to each focus.

For a traversal `t : Traversal s t a b`, applicative `F`, and function `f : a → F b`:
- `traverse t f s` applies `f` to each focus, collecting the effects

Implementation: Uses the existing monomorphic `Collimator.Traversal.traverse` function.
-/
instance : HasTraverse Traversal where
  traverse {_s _t _a _b F} [Applicative F] t f s :=
    Traversal.traverse' t f s

end Collimator.Poly
