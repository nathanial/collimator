import Collimator.Optics.Traversal
import Collimator.Optics.Fold

/-!
# Plated: Recursive Structure Traversals

The `Plated` typeclass provides optics for working with recursive
data structures. It enables powerful transformations like:

- `children` - Access immediate children of the same type
- `universe` - Access all descendants (transitive closure)
- `transform` - Bottom-up transformation
- `rewrite` - Iterated rewriting until fixpoint
- `contexts` - Access each position with its context

## Defining Plated Instances

For a recursive type, implement `plate` to traverse immediate children:

```lean
inductive Tree (α : Type) where
  | leaf : α → Tree α
  | node : Tree α → Tree α → Tree α

instance : Plated (Tree α) where
  plate := traversal fun f t =>
    match t with
    | Tree.leaf _ => pure t  -- leaves have no children
    | Tree.node l r => pure Tree.node <*> f l <*> f r
```

## Example Usage

```lean
-- Double all values in nested lists
transform (over traversed (* 2)) [[1, 2], [3, [4, 5]]]

-- Find all numbers in a tree
toListOf universe myTree
```
-/

namespace Collimator.Combinators.Plated

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

/--
Access the immediate children of a plated structure.

This is just the `plate` traversal from the typeclass.
-/
@[inline] def children {α : Type} [Plated α] : Traversal' α α :=
  Plated.plate

/--
Collect all immediate children into a list.
-/
def childrenOf {α : Type} [Plated α] (x : α) : List α :=
  Fold.toListTraversal Plated.plate x

/--
Apply a transformation to all immediate children.
-/
def overChildren {α : Type} [Plated α] (f : α → α) (x : α) : α :=
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
partial def transform {α : Type} [Plated α] (f : α → α) (x : α) : α :=
  f (overChildren (transform f) x)

/--
Transform a structure top-down.

Applies the transformation first, then recursively transforms children.
-/
partial def transformDown {α : Type} [Plated α] (f : α → α) (x : α) : α :=
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
partial def rewrite {α : Type} [Plated α] (f : α → Option α) (x : α) : α :=
  let x' := overChildren (rewrite f) x
  match f x' with
  | some y => rewrite f y  -- Keep rewriting if f succeeds
  | none => x'             -- Done rewriting this node

/--
Rewrite top-down: try to rewrite at each node before recursing.
-/
partial def rewriteDown {α : Type} [Plated α] (f : α → Option α) (x : α) : α :=
  let x' := match f x with
    | some y => y
    | none => x
  overChildren (rewriteDown f) x'

/--
Descend one level into children, applying a monadic action.

This is the effectful version of `overChildren`.
-/
def descendM {α : Type} {M : Type → Type} [Plated α] [Monad M]
    (f : α → M α) (x : α) : M α :=
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
partial def universeList {α : Type} [Plated α] (x : α) : List α :=
  x :: (childrenOf x).flatMap universeList

/--
Count the total number of nodes in a recursive structure.
-/
partial def cosmosCount {α : Type} [Plated α] (x : α) : Nat :=
  1 + (childrenOf x).foldl (fun acc child => acc + cosmosCount child) 0

/--
Find the maximum depth of a recursive structure.
-/
partial def depth {α : Type} [Plated α] (x : α) : Nat :=
  let childDepths := (childrenOf x).map depth
  1 + (childDepths.foldl max 0)

/--
Check if a predicate holds for all nodes in the structure.
-/
partial def allOf {α : Type} [Plated α] (p : α → Bool) (x : α) : Bool :=
  p x && (childrenOf x).all (allOf p)

/--
Check if a predicate holds for any node in the structure.
-/
partial def anyOf {α : Type} [Plated α] (p : α → Bool) (x : α) : Bool :=
  p x || (childrenOf x).any (anyOf p)

/--
Find the first node matching a predicate (depth-first).
-/
partial def findOf {α : Type} [Plated α] (p : α → Bool) (x : α) : Option α :=
  if p x then some x
  else (childrenOf x).findSome? (findOf p)

/-! ## Common Instances -/

/-- Lists are plated: the children of a list are its tail sublists.
    Note: This is one interpretation. Another would be no children (leaves only). -/
instance instPlatedList {α : Type} : Plated (List α) where
  plate := Collimator.traversal
    (fun {F : Type → Type} [Applicative F]
      (f : List α → F (List α)) (xs : List α) =>
        match xs with
        | [] => pure []
        | x :: rest => Functor.map (List.cons x) (f rest))

/-- Option has no recursive structure (no children). -/
instance instPlatedOption {α : Type} : Plated (Option α) where
  plate := Collimator.traversal
    (fun {F : Type → Type} [Applicative F]
      (_f : Option α → F (Option α)) (x : Option α) =>
        pure x)

end Collimator.Combinators.Plated
