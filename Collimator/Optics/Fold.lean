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

/-!
## Foldable Typeclass

`Foldable` captures optics that can extract a list of foci from a structure.
This allows `toList`, `sumOf`, `lengthOf`, etc. to work polymorphically across
`Fold`, `Lens`, `Prism`, `AffineTraversal`, and `Traversal`.
-/

/-- Typeclass for optics that can fold/collect their foci into a list. -/
class Foldable (optic : Type → Type → Type → Type → Type 1) where
  /-- Collect all foci into a list. -/
  foldToList : ∀ {s t a b : Type} [Inhabited (List a)], optic s t a b → s → List a

-- Instance for Fold
instance : Foldable Fold where
  foldToList fld s₀ :=
    let forget : Forget (List _) _ _ := fun x => [x]
    let lifted := fld (P := Forget (List _)) forget
    lifted s₀

-- Instance for Lens
instance : Foldable Lens where
  foldToList l s₀ :=
    let forget : Forget (List _) _ _ := fun x => [x]
    let lifted := l (P := Forget (List _)) forget
    lifted s₀

-- Instance for Prism
instance : Foldable Prism where
  foldToList p s₀ :=
    let forget : Forget (List _) _ _ := fun x => [x]
    let lifted := p (P := Forget (List _)) forget
    lifted s₀

-- Instance for AffineTraversal
instance : Foldable AffineTraversal where
  foldToList aff s₀ :=
    let forget : Forget (List _) _ _ := fun x => [x]
    let lifted := aff (P := Forget (List _)) forget
    lifted s₀

-- Instance for Traversal (uses Wandering instance of Forget)
instance : Foldable Traversal where
  foldToList tr s₀ :=
    let forget : Forget (List _) _ _ := fun x => [x]
    let lifted := tr (P := Forget (List _)) forget
    lifted s₀

-- Instance for Iso
instance : Foldable Iso where
  foldToList i s₀ :=
    let forget : Forget (List _) _ _ := fun x => [x]
    let lifted := i (P := Forget (List _)) forget
    lifted s₀

namespace Fold

/-- Every lens gives a fold that observes its focus. -/
def ofLens {s t a b : Type}
    (l : Lens s t a b) : Collimator.Fold s t a b :=
  fun {P} [Profunctor P] [Strong P] [Choice P] pab => l (P := P) pab

/-- Every affine traversal can be used as a fold. -/
def ofAffine {s t a b : Type}
    (aff : Collimator.AffineTraversal s t a b) : Collimator.Fold s t a b :=
  fun {P} [Profunctor P] [Strong P] [Choice P] pab => aff (P := P) pab

/-
Note: There is no general `Traversal → Fold` coercion because `Traversal` requires
`Wandering P` while `Fold` only provides `Strong P + Choice P`. You cannot construct
a `Wandering` instance from just `Strong + Choice`.

However, for specific operations like `toList`, we use `Forget R` which has a `Wandering`
instance (when R has `One`, `Mul`, `Inhabited`), so traversals work with those functions.

Use `toListTraversal`, `sumOfTraversal`, etc. for traversals, or use the coercion
from `Lens`/`Prism`/`AffineTraversal` to `Fold` for those optic types.
-/

/-- Collect all focuses of a fold into a list. -/
def toList {s a : Type} [Inhabited (List a)]
    (fld : Fold' s a) (s₀ : s) : List a :=
  let forget : Forget (List a) a a := fun x => [x]
  let lifted :=
    fld (P := fun α β => Forget (List a) α β) forget
  lifted s₀

/-- Collect all focuses of a traversal into a list using Forget's Wandering instance. -/
def toListTraversal {s a : Type} [Inhabited (List a)]
    (tr : Traversal' s a) (s₀ : s) : List a :=
  let forget : Forget (List a) a a := fun x => [x]
  let lifted := tr (P := Forget (List a)) forget
  lifted s₀

/-!
## Traversal-specific fold operations

These functions provide the same functionality as the `Fold'` versions but work
directly with `Traversal'`. They use `Forget R` which has a `Wandering` instance.
-/

/-- Check if any focus of a traversal matches a predicate. -/
def anyOfTraversal {s a : Type} [Inhabited (List a)]
    (tr : Traversal' s a) (pred : a → Bool) (s₀ : s) : Bool :=
  (toListTraversal tr s₀).any pred

/-- Check if all foci of a traversal match a predicate. -/
def allOfTraversal {s a : Type} [Inhabited (List a)]
    (tr : Traversal' s a) (pred : a → Bool) (s₀ : s) : Bool :=
  (toListTraversal tr s₀).all pred

/-- Find the first focus of a traversal that matches a predicate. -/
def findOfTraversal {s a : Type} [Inhabited (List a)]
    (tr : Traversal' s a) (pred : a → Bool) (s₀ : s) : Option a :=
  (toListTraversal tr s₀).find? pred

/-- Count the number of foci in a traversal. -/
def lengthOfTraversal {s a : Type} [Inhabited (List a)]
    (tr : Traversal' s a) (s₀ : s) : Nat :=
  (toListTraversal tr s₀).length

/-- Sum all numeric foci of a traversal. -/
def sumOfTraversal {s a : Type} [Inhabited (List a)] [Add a] [OfNat a 0]
    (tr : Traversal' s a) (s₀ : s) : a :=
  (toListTraversal tr s₀).foldl (· + ·) 0

/-- Check if a traversal has no foci. -/
def nullOfTraversal {s a : Type} [Inhabited (List a)]
    (tr : Traversal' s a) (s₀ : s) : Bool :=
  (toListTraversal tr s₀).isEmpty

/-- Compose a lens with a fold to focus deeper. -/
@[inline] def composeLensFold
    {s t a b u v : Type}
    (outer : Lens s t a b) (inner : Collimator.Fold a b u v) :
    Collimator.Fold s t u v :=
  fun {P} [Profunctor P] [Strong P] [Choice P] puv =>
    outer (P := P) (inner (P := P) puv)

/-- Compose two folds to read through nested structures. -/
@[inline] def composeFold
    {s t a b u v : Type}
    (outer : Collimator.Fold s t a b) (inner : Collimator.Fold a b u v) :
    Collimator.Fold s t u v :=
  fun {P} [Profunctor P] [Strong P] [Choice P] puv =>
    outer (P := P) (inner (P := P) puv)

scoped infixr:80 " ∘ₗf " => composeLensFold
scoped infixr:80 " ∘f " => composeFold

/--
Check if any focus of the fold matches a predicate.

```lean
anyOf traversed (· > 3) [1, 2, 5]  -- true
anyOf traversed (· > 10) [1, 2, 5] -- false
```
-/
def anyOf {s a : Type} [Inhabited (List a)]
    (fld : Fold' s a) (pred : a → Bool) (s₀ : s) : Bool :=
  (toList fld s₀).any pred

/--
Check if all foci of the fold match a predicate.

```lean
allOf traversed (· > 0) [1, 2, 3]  -- true
allOf traversed (· > 2) [1, 2, 3]  -- false
```
-/
def allOf {s a : Type} [Inhabited (List a)]
    (fld : Fold' s a) (pred : a → Bool) (s₀ : s) : Bool :=
  (toList fld s₀).all pred

/--
Find the first focus that matches a predicate.

```lean
findOf traversed (· > 2) [1, 2, 3, 4]  -- some 3
findOf traversed (· > 10) [1, 2, 3]    -- none
```
-/
def findOf {s a : Type} [Inhabited (List a)]
    (fld : Fold' s a) (pred : a → Bool) (s₀ : s) : Option a :=
  (toList fld s₀).find? pred

/--
Count the number of foci in the fold.

```lean
lengthOf traversed [1, 2, 3, 4, 5]  -- 5
lengthOf traversed []               -- 0
```
-/
def lengthOf {s a : Type} [Inhabited (List a)]
    (fld : Fold' s a) (s₀ : s) : Nat :=
  (toList fld s₀).length

/--
Sum all numeric foci.

```lean
sumOf traversed [1, 2, 3, 4, 5]  -- 15
```
-/
def sumOf {s a : Type} [Inhabited (List a)] [Add a] [OfNat a 0]
    (fld : Fold' s a) (s₀ : s) : a :=
  (toList fld s₀).foldl (· + ·) 0

/--
Check if the fold has no foci.

```lean
nullOf traversed []       -- true
nullOf traversed [1, 2]   -- false
```
-/
def nullOf {s a : Type} [Inhabited (List a)]
    (fld : Fold' s a) (s₀ : s) : Bool :=
  (toList fld s₀).isEmpty

end Fold

/-!
## Polymorphic Fold Operations

These functions work with any optic that has a `Foldable` instance, including
`Lens`, `Prism`, `AffineTraversal`, `Traversal`, and `Fold`.

Example usage:
```lean
-- All of these work with `toListOf`:
toListOf nameLens person           -- Lens
toListOf somePrism' maybeValue     -- Prism
toListOf affineTraversal structure -- AffineTraversal
toListOf traversed list            -- Traversal
toListOf fold structure            -- Fold
```
-/

/-- Collect all foci of any foldable optic into a list. -/
def toListOf {optic : Type → Type → Type → Type → Type 1} [Foldable optic]
    {s t a b : Type} [Inhabited (List a)] (o : optic s t a b) (s₀ : s) : List a :=
  Foldable.foldToList o s₀

/-- Check if any focus matches a predicate. Works with any foldable optic. -/
def anyOf {optic : Type → Type → Type → Type → Type 1} [Foldable optic]
    {s t a b : Type} [Inhabited (List a)] (o : optic s t a b) (pred : a → Bool) (s₀ : s) : Bool :=
  (toListOf o s₀).any pred

/-- Check if all foci match a predicate. Works with any foldable optic. -/
def allOf {optic : Type → Type → Type → Type → Type 1} [Foldable optic]
    {s t a b : Type} [Inhabited (List a)] (o : optic s t a b) (pred : a → Bool) (s₀ : s) : Bool :=
  (toListOf o s₀).all pred

/-- Find first focus matching a predicate. Works with any foldable optic. -/
def findOf {optic : Type → Type → Type → Type → Type 1} [Foldable optic]
    {s t a b : Type} [Inhabited (List a)] (o : optic s t a b) (pred : a → Bool) (s₀ : s) : Option a :=
  (toListOf o s₀).find? pred

/-- Count the number of foci. Works with any foldable optic. -/
def lengthOf {optic : Type → Type → Type → Type → Type 1} [Foldable optic]
    {s t a b : Type} [Inhabited (List a)] (o : optic s t a b) (s₀ : s) : Nat :=
  (toListOf o s₀).length

/-- Sum all numeric foci. Works with any foldable optic. -/
def sumOf {optic : Type → Type → Type → Type → Type 1} [Foldable optic]
    {s t a b : Type} [Inhabited (List a)] [Add a] [OfNat a 0] (o : optic s t a b) (s₀ : s) : a :=
  (toListOf o s₀).foldl (· + ·) 0

/-- Check if the optic has no foci. Works with any foldable optic. -/
def nullOf {optic : Type → Type → Type → Type → Type 1} [Foldable optic]
    {s t a b : Type} [Inhabited (List a)] (o : optic s t a b) (s₀ : s) : Bool :=
  (toListOf o s₀).isEmpty

/-- Get the first focus if it exists. Works with any foldable optic. -/
def firstOf {optic : Type → Type → Type → Type → Type 1} [Foldable optic]
    {s t a b : Type} [Inhabited (List a)] (o : optic s t a b) (s₀ : s) : Option a :=
  (toListOf o s₀).head?

/-- Get the last focus if it exists. Works with any foldable optic. -/
def lastOf {optic : Type → Type → Type → Type → Type 1} [Foldable optic]
    {s t a b : Type} [Inhabited (List a)] (o : optic s t a b) (s₀ : s) : Option a :=
  (toListOf o s₀).getLast?

end Collimator
