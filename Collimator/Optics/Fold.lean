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

/--
Check if any focus of the fold matches a predicate.

```lean
anyOf traversed (· > 3) [1, 2, 5]  -- true
anyOf traversed (· > 10) [1, 2, 5] -- false
```
-/
def anyOf {s a : Type _} [Inhabited (List a)]
    (fld : Fold' s a) (pred : a → Bool) (s₀ : s) : Bool :=
  (toList fld s₀).any pred

/--
Check if all foci of the fold match a predicate.

```lean
allOf traversed (· > 0) [1, 2, 3]  -- true
allOf traversed (· > 2) [1, 2, 3]  -- false
```
-/
def allOf {s a : Type _} [Inhabited (List a)]
    (fld : Fold' s a) (pred : a → Bool) (s₀ : s) : Bool :=
  (toList fld s₀).all pred

/--
Find the first focus that matches a predicate.

```lean
findOf traversed (· > 2) [1, 2, 3, 4]  -- some 3
findOf traversed (· > 10) [1, 2, 3]    -- none
```
-/
def findOf {s a : Type _} [Inhabited (List a)]
    (fld : Fold' s a) (pred : a → Bool) (s₀ : s) : Option a :=
  (toList fld s₀).find? pred

/--
Count the number of foci in the fold.

```lean
lengthOf traversed [1, 2, 3, 4, 5]  -- 5
lengthOf traversed []               -- 0
```
-/
def lengthOf {s a : Type _} [Inhabited (List a)]
    (fld : Fold' s a) (s₀ : s) : Nat :=
  (toList fld s₀).length

/--
Sum all numeric foci.

```lean
sumOf traversed [1, 2, 3, 4, 5]  -- 15
```
-/
def sumOf {s a : Type _} [Inhabited (List a)] [Add a] [OfNat a 0]
    (fld : Fold' s a) (s₀ : s) : a :=
  (toList fld s₀).foldl (· + ·) 0

/--
Check if the fold has no foci.

```lean
nullOf traversed []       -- true
nullOf traversed [1, 2]   -- false
```
-/
def nullOf {s a : Type _} [Inhabited (List a)]
    (fld : Fold' s a) (s₀ : s) : Bool :=
  (toList fld s₀).isEmpty

end Fold

end Collimator
