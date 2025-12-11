import Collimator.Core
import Collimator.Optics

/-!
# Collimator Combinators

This module provides optic combinators for working with profunctor optics.

## Composition

With type alias optics, standard function composition (`∘`) works naturally:

```lean
-- Compose two lenses
let composed := outerLens ∘ innerLens

-- Compose a lens with a prism (gives AffineTraversal)
let affine := myLens ∘ myPrism

-- Compose a lens with a traversal (gives Traversal)
let trav := myLens ∘ myTraversal
```

The profunctor constraints are automatically propagated by Lean's type system.

## Combinators Provided

- **Filtering**: `filtered`, `filteredList`, `ifilteredList`
- **Safe List Ops**: `_head`, `_last`, `taking`, `dropping`
- **Prism Ops**: `orElse`, `affineFromPartial`
- **Indexed**: `ix`, `atLens` for index-based access
- **Bitraversal**: `both`, `beside`, `chosen` for bifunctors
- **Plated**: `transform`, `rewrite`, `universe` for recursive structures
-/

namespace Collimator.Combinators

open Collimator
open Collimator.Core
open Collimator.Setter
open Collimator.Traversal


/-! ## Filtering Combinators -/

section Filtering
variable {s a : Type}

/--
Restrict a traversal to focuses that satisfy a predicate. The traversal is
monomorphic because the predicate must be evaluated on both the input and the
output type.
-/
def filtered (tr : Traversal' s a) (pred : a → Bool) : Traversal' s a :=
  Collimator.traversal
    (fun {F : Type → Type} [Applicative F] (f : a → F a) (s₀ : s) =>
      Traversal.traverse' (tr := tr)
        (fun a => if pred a then f a else pure a)
        s₀)

/--
Focus only on list elements matching a predicate.

Elements that don't match the predicate are left unchanged during modification.

```lean
-- Double only positive numbers
over (filteredList (· > 0)) (· * 2) [-1, 2, -3, 4]
-- Result: [-1, 4, -3, 8]
```
-/
def filteredList (pred : a → Bool) : Traversal' (List a) a :=
  Collimator.traversal
    (fun {F : Type → Type} [Applicative F] (f : a → F a) (xs : List a) =>
      let rec go : List a → F (List a)
        | [] => pure []
        | x :: rest =>
            if pred x then
              (· :: ·) <$> f x <*> go rest
            else
              (x :: ·) <$> go rest
      go xs)

/--
Focus on list elements where a predicate on both index and value holds.

The index is 0-based.

```lean
-- Modify only elements at even indices
over (ifilteredList fun i _ => i % 2 == 0) (· ++ "!") ["a", "b", "c", "d"]
-- Result: ["a!", "b", "c!", "d"]
```
-/
def ifilteredList (pred : Nat → a → Bool) : Traversal' (List a) a :=
  Collimator.traversal
    (fun {F : Type → Type} [Applicative F] (f : a → F a) (xs : List a) =>
      let rec go : Nat → List a → F (List a)
        | _, [] => pure []
        | idx, x :: rest =>
            if pred idx x then
              (· :: ·) <$> f x <*> go (idx + 1) rest
            else
              (x :: ·) <$> go (idx + 1) rest
      go 0 xs)

end Filtering


/-! ## Safe List Operations -/

section ListOps
variable {a : Type}

/--
Safely access the head of a list.

Returns `AffineTraversal` because the list may be empty. Use with `preview`
to safely extract or `over`/`set` to modify if present.

```lean
preview _head [1, 2, 3]  -- some 1
preview _head []         -- none
over _head (· * 10) [1, 2, 3]  -- [10, 2, 3]
over _head (· * 10) []         -- []
```
-/
def _head : AffineTraversal' (List a) a :=
  fun {P} [Profunctor P] [Strong P] [Choice P] pab =>
    Profunctor.dimap
      (fun xs : List a => match xs with
        | [] => Sum.inl []
        | x :: rest => Sum.inr (x, rest))
      (fun
        | Sum.inl xs => xs
        | Sum.inr (x, rest) => x :: rest)
      (Choice.right (Strong.first pab))

/--
Safely access the last element of a list.

Returns `AffineTraversal` because the list may be empty.

```lean
preview _last [1, 2, 3]  -- some 3
preview _last []         -- none
over _last (· * 10) [1, 2, 3]  -- [1, 2, 30]
```
-/
def _last : AffineTraversal' (List a) a :=
  fun {P} [Profunctor P] [Strong P] [Choice P] pab =>
    let splitLast : List a → Sum (List a) (List a × a) :=
      fun xs =>
        let rec getInitLast : List a → List a → Option (List a × a)
          | _acc, [] => none
          | acc, [x] => some (acc.reverse, x)
          | acc, x :: rest => getInitLast (x :: acc) rest
        match getInitLast [] xs with
        | none => Sum.inl []
        | some (init, last) => Sum.inr (init, last)
    Profunctor.dimap
      splitLast
      (fun
        | Sum.inl xs => xs
        | Sum.inr (init, last) => init ++ [last])
      (Choice.right (Strong.second pab))

/--
Traverse the first `n` elements of a list.

Elements beyond the first `n` are left unchanged.

```lean
over (taking 2) (· * 10) [1, 2, 3, 4]  -- [10, 20, 3, 4]
over (taking 0) (· * 10) [1, 2, 3]     -- [1, 2, 3]
over (taking 10) (· * 10) [1, 2]       -- [10, 20]
```
-/
def taking (n : Nat) : Traversal' (List a) a :=
  Collimator.traversal
    (fun {F : Type → Type} [Applicative F] (f : a → F a) (xs : List a) =>
      let (prefix_, suffix) := xs.splitAt n
      let rec traverseList : List a → F (List a)
        | [] => pure []
        | x :: rest => (· :: ·) <$> f x <*> traverseList rest
      (· ++ suffix) <$> traverseList prefix_)

/--
Skip the first `n` elements and traverse the rest.

The first `n` elements are left unchanged.

```lean
over (dropping 2) (· * 10) [1, 2, 3, 4]  -- [1, 2, 30, 40]
over (dropping 0) (· * 10) [1, 2, 3]     -- [10, 20, 30]
over (dropping 10) (· * 10) [1, 2]       -- [1, 2]
```
-/
def dropping (n : Nat) : Traversal' (List a) a :=
  Collimator.traversal
    (fun {F : Type → Type} [Applicative F] (f : a → F a) (xs : List a) =>
      let (prefix_, suffix) := xs.splitAt n
      let rec traverseList : List a → F (List a)
        | [] => pure []
        | x :: rest => (· :: ·) <$> f x <*> traverseList rest
      (prefix_ ++ ·) <$> traverseList suffix)

end ListOps


/-! ## Prism Combinators -/

section PrismOps
variable {s a : Type}

/--
Try the first prism, and if it fails, try the second.

The result is an `AffineTraversal` because both prisms might fail.

```lean
-- Create a prism that matches either even OR divisible by 3
def evenOrDiv3 : AffineTraversal' Int Int :=
  orElse
    (prismFromPartial (fun n => if n % 2 == 0 then some n else none) id)
    (prismFromPartial (fun n => if n % 3 == 0 then some n else none) id)

preview evenOrDiv3 4   -- some 4 (even)
preview evenOrDiv3 9   -- some 9 (div by 3)
preview evenOrDiv3 7   -- none (neither)
```
-/
def orElse (p1 : Prism' s a) (p2 : Prism' s a) : AffineTraversal' s a :=
  fun {P} [Profunctor P] [Strong P] [Choice P] pab =>
    let tryBoth : s → Sum s (a × s) := fun s =>
      match preview' p1 s with
      | some a => Sum.inr (a, s)
      | none => match preview' p2 s with
        | some a => Sum.inr (a, s)
        | none => Sum.inl s
    Profunctor.dimap
      tryBoth
      (fun
        | Sum.inl s => s
        | Sum.inr (a, origS) =>
          match preview' p1 origS with
          | some _ => review' p1 a
          | none => review' p2 a)
      (Choice.right (Strong.first pab))

/--
Construct an affine traversal from a preview and set function.

This is useful when you have partial getter/setter semantics.

```lean
def headAffine : AffineTraversal' (List a) a :=
  affineFromPartial
    (fun xs => xs.head?)
    (fun xs a => match xs with
      | [] => []
      | _ :: rest => a :: rest)
```
-/
def affineFromPartial
    (preview_ : s → Option a)
    (set_ : s → a → s) : AffineTraversal' s a :=
  fun {P} [Profunctor P] [Strong P] [Choice P] pab =>
    Profunctor.dimap
      (fun s => match preview_ s with
        | some a => Sum.inr (a, s)
        | none => Sum.inl s)
      (fun
        | Sum.inl s => s
        | Sum.inr (a, s) => set_ s a)
      (Choice.right (Strong.first pab))

end PrismOps

end Collimator.Combinators


/-! ## Indexed Optics -/

namespace Collimator.Indexed

open Collimator

section
variable {ι s a : Type}

/--
Capability for focusing a single position identified by an index.
-/
class HasIx (ι : Type) (s : Type) (a : Type) where
  ix : ι → Traversal' s a

/--
Capability for viewing or updating an optional focus at an index.
-/
class HasAt (ι : Type) (s : Type) (a : Type) where
  focus : ι → Lens' s (Option a)

/--
Retrieve the traversal focusing a particular index.
-/
@[inline] def ix [HasIx ι s a] (i : ι) : Traversal' s a :=
  HasIx.ix i

/--
Retrieve the lens exposing an optional focus at a particular index.
-/
@[inline] def atLens [HasAt ι s a] (i : ι) : Lens' s (Option a) :=
  HasAt.focus i

end

end Collimator.Indexed


/-! ## Bifunctor Traversals -/

namespace Collimator.Combinators.Bitraversal

open Collimator

section
variable {α β : Type}

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
def both : Traversal (α × α) (β × β) α β :=
  Collimator.traversal
    (fun {F : Type → Type} [Applicative F] (f : α → F β) (pair : α × α) =>
      pure Prod.mk <*> f pair.1 <*> f pair.2)

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
def chosen : Traversal (Sum α α) (Sum β β) α β :=
  Collimator.traversal
    (fun {F : Type → Type} [Applicative F] (f : α → F β) (s : Sum α α) =>
      match s with
      | Sum.inl a => Functor.map Sum.inl (f a)
      | Sum.inr a => Functor.map Sum.inr (f a))

/--
Swap the components of a homogeneous pair.

This is an isomorphism, but provided here for completeness with
bifunctor operations.
-/
def swapped : Iso' (α × α) (α × α) :=
  Collimator.iso (forward := fun (a, b) => (b, a)) (back := fun (a, b) => (b, a))

/--
Swap the branches of a homogeneous sum.
-/
def swappedSum : Iso' (Sum α α) (Sum α α) :=
  Collimator.iso
    (forward := fun
      | Sum.inl a => Sum.inr a
      | Sum.inr a => Sum.inl a)
    (back := fun
      | Sum.inl a => Sum.inr a
      | Sum.inr a => Sum.inl a)

end

/-- Monomorphic version of `both`. -/
def both' (α : Type) : Traversal' (α × α) α := both

/-- Monomorphic version of `chosen`. -/
def chosen' (α : Type) : Traversal' (Sum α α) α := chosen

section Beside
variable {s t s' t' a b : Type}

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
def beside (l : Traversal s t a b) (r : Traversal s' t' a b)
    : Traversal (s × s') (t × t') a b :=
  Collimator.traversal
    (fun {F : Type → Type} [Applicative F] (f : a → F b) (pair : s × s') =>
      pure Prod.mk <*> Traversal.traverse' l f pair.1 <*> Traversal.traverse' r f pair.2)

end Beside

/-- Monomorphic version of `beside`. -/
def beside' {s s' a : Type} (l : Traversal' s a) (r : Traversal' s' a)
    : Traversal' (s × s') a := beside l r

end Collimator.Combinators.Bitraversal


/-! ## Plated: Recursive Structure Traversals -/

namespace Collimator.Combinators

open Collimator

/--
Typeclass for types with a self-similar recursive structure.

The `plate` traversal focuses on immediate children of the same type.
This enables generic recursive operations like `transform` and `universe`.

## Laws

- `plate` should only focus on immediate children, not deeper descendants
- `plate` should preserve the structure when the function is `pure`
-/
class Plated (α : Type) where
  /-- Traversal focusing on immediate children of the same type. -/
  plate : Traversal' α α

section
variable {α : Type} [Plated α]

/--
Access the immediate children of a plated structure.

This is just the `plate` traversal from the typeclass.
-/
@[inline] def children : Traversal' α α :=
  Plated.plate

/--
Collect all immediate children into a list.
-/
def childrenOf (x : α) : List α :=
  Fold.toListTraversal Plated.plate x

/--
Apply a transformation to all immediate children.
-/
def overChildren (f : α → α) (x : α) : α :=
  Traversal.over' Plated.plate f x

/--
Transform a structure bottom-up.

Applies the transformation to all descendants first (recursively),
then applies it to the result. This ensures that when `f` is called
on a node, all its children have already been transformed.

## Example

```lean
-- Simplify arithmetic expressions bottom-up
def simplify : Expr → Expr
  | Expr.add (Expr.num 0) e => e
  | Expr.add e (Expr.num 0) => e
  | e => e

transform simplify expr  -- applies simplify to all subexpressions
```
-/
partial def transform (f : α → α) (x : α) : α :=
  f (overChildren (transform f) x)

/--
Transform a structure top-down.

Applies the transformation first, then recursively transforms children.
-/
partial def transformDown (f : α → α) (x : α) : α :=
  overChildren (transformDown f) (f x)

/--
Rewrite a structure by repeatedly applying a partial function.

The rewrite function is applied repeatedly until it returns `none`,
at which point we recurse into children. This continues until no
more rewrites are possible anywhere in the structure.

## Example

```lean
-- Repeatedly simplify until no more simplifications possible
def trySimplify : Expr → Option Expr
  | Expr.add (Expr.num 0) e => some e
  | _ => none

rewrite trySimplify expr
```
-/
partial def rewrite (f : α → Option α) (x : α) : α :=
  let x' := overChildren (rewrite f) x
  match f x' with
  | some y => rewrite f y
  | none => x'

/--
Rewrite top-down: try to rewrite at each node before recursing.
-/
partial def rewriteDown (f : α → Option α) (x : α) : α :=
  let x' := match f x with
    | some y => y
    | none => x
  overChildren (rewriteDown f) x'

/--
Descend one level into children, applying a monadic action.

This is the effectful version of `overChildren`.
-/
def descendM {M : Type → Type} [Monad M] (f : α → M α) (x : α) : M α :=
  Traversal.traverse' Plated.plate f x

/--
Descend into all descendants (the transitive closure of `children`).

Collects all values reachable by repeatedly following `plate`.
Includes the root value itself.

## Example

```lean
-- Get all subexpressions of an expression
toListOf universe expr
```
-/
partial def universeList (x : α) : List α :=
  x :: (childrenOf x).flatMap universeList

/--
Count the total number of nodes in a recursive structure.
-/
partial def cosmosCount (x : α) : Nat :=
  1 + (childrenOf x).foldl (fun acc child => acc + cosmosCount child) 0

/--
Find the maximum depth of a recursive structure.
-/
partial def depth (x : α) : Nat :=
  let childDepths := (childrenOf x).map depth
  1 + (childDepths.foldl max 0)

/--
Check if a predicate holds for all nodes in the structure.
-/
partial def allOf (p : α → Bool) (x : α) : Bool :=
  p x && (childrenOf x).all (allOf p)

/--
Check if a predicate holds for any node in the structure.
-/
partial def anyOf (p : α → Bool) (x : α) : Bool :=
  p x || (childrenOf x).any (anyOf p)

/--
Find the first node matching a predicate (depth-first).
-/
partial def findOf (p : α → Bool) (x : α) : Option α :=
  if p x then some x
  else (childrenOf x).findSome? (findOf p)

end

/-! ## Common Instances -/

/-- Lists are plated: the children of a list are its tail sublists.
    Note: This is one interpretation. Another would be no children (leaves only). -/
instance instPlatedList {α : Type} : Plated (List α) where
  plate := Collimator.traversal
    (fun {F : Type → Type} [Applicative F] (f : List α → F (List α)) (xs : List α) =>
      match xs with
      | [] => pure []
      | x :: rest => Functor.map (List.cons x) (f rest))

/-- Option has no recursive structure (no children). -/
instance instPlatedOption {α : Type} : Plated (Option α) where
  plate := Collimator.traversal
    (fun {F : Type → Type} [Applicative F] (_f : Option α → F (Option α)) (x : Option α) =>
      pure x)

end Collimator.Combinators
