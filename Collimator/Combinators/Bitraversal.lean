import Collimator.Optics.Traversal
import Collimator.Optics.Affine
import Collimator.Optics.Iso

/-!
# Bifunctor Traversals

Traversals for bifunctor-like structures where both "sides" contain
the same type.

## Key Combinators

- `both` - Traverse both components of a homogeneous pair `(α × α)`
- `beside` - Traverse two components with different traversals
- `chosen` - Traverse whichever branch is present in `Sum α α`

## Examples

```lean
-- Double both components of a pair
over both (* 2) (3, 5)  -- (6, 10)

-- Negate whichever value is present
over chosen (· * -1) (Sum.inl 42)  -- Sum.inl (-42)
over chosen (· * -1) (Sum.inr 99)  -- Sum.inr (-99)
```
-/

namespace Collimator.Combinators.Bitraversal

open Collimator


/--
Traverse both components of a homogeneous pair.

This is useful when you have a pair of the same type and want to
apply the same transformation to both elements.

## Example

```lean
over both String.toUpper ("hello", "world")
-- ("HELLO", "WORLD")

-- Collect both values
toListOf both (1, 2)
-- [1, 2]
```
-/
def both {α β : Type} : Traversal (α × α) (β × β) α β :=
  Collimator.traversal
    (fun {F : Type → Type} [Applicative F]
      (f : α → F β) (pair : α × α) =>
        pure Prod.mk <*> f pair.1 <*> f pair.2)

/-- Monomorphic version of `both`. -/
def both' (α : Type) : Traversal' (α × α) α := both

/--
Traverse both parts of a pair, using separate traversals for each.

Given a traversal for the left component and one for the right,
create a traversal that visits all `a` foci in both parts of the pair.

## Example

```lean
-- Given a pair of lists, traverse all elements
beside traversed traversed : Traversal' (List Int × List Int) Int

over (beside traversed traversed) (· + 1) ([1, 2], [3, 4])
-- ([2, 3], [4, 5])

-- Collect all values from both sides
toListOf (beside traversed traversed) (["a", "b"], ["c"])
-- ["a", "b", "c"]
```
-/
def beside {s t s' t' a b : Type}
    (l : Traversal s t a b) (r : Traversal s' t' a b)
    : Traversal (s × s') (t × t') a b :=
  Collimator.traversal
    (fun {F : Type → Type} [Applicative F]
      (f : a → F b) (pair : s × s') =>
        -- Traverse left side with l, right side with r, combine results
        pure Prod.mk <*> Traversal.traverse' l f pair.1 <*> Traversal.traverse' r f pair.2)

/-- Monomorphic version of `beside`. -/
def beside' {s s' a : Type}
    (l : Traversal' s a) (r : Traversal' s' a)
    : Traversal' (s × s') a := beside l r

/--
Traverse whichever branch is present in a homogeneous sum.

This traversal always has exactly one focus - either the left
or right value, whichever is present.

## Example

```lean
over chosen (* 2) (Sum.inl 5)   -- Sum.inl 10
over chosen (* 2) (Sum.inr 7)   -- Sum.inr 14

preview chosen (Sum.inl "hi")   -- some "hi"
```
-/
def chosen {α β : Type} : Traversal (Sum α α) (Sum β β) α β :=
  Collimator.traversal
    (fun {F : Type → Type} [Applicative F]
      (f : α → F β) (s : Sum α α) =>
        match s with
        | Sum.inl a => Functor.map Sum.inl (f a)
        | Sum.inr a => Functor.map Sum.inr (f a))

/-- Monomorphic version of `chosen`. -/
def chosen' (α : Type) : Traversal' (Sum α α) α := chosen

/--
Swap the components of a homogeneous pair.

This is an isomorphism, but provided here for completeness with
bifunctor operations.
-/
def swapped {α : Type} : Iso' (α × α) (α × α) :=
  Collimator.iso (forward := fun (a, b) => (b, a)) (back := fun (a, b) => (b, a))

/--
Swap the branches of a homogeneous sum.
-/
def swappedSum {α : Type} : Iso' (Sum α α) (Sum α α) :=
  Collimator.iso
    (forward := fun
      | Sum.inl a => Sum.inr a
      | Sum.inr a => Sum.inl a)
    (back := fun
      | Sum.inl a => Sum.inr a
      | Sum.inr a => Sum.inl a)

end Collimator.Combinators.Bitraversal
