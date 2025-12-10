import Batteries
import Collimator.Core.Profunctor
import Collimator.Core.Wandering
import Collimator.Optics.Types
import Collimator.Concrete.FunArrow
import Collimator.Concrete.Star

namespace Collimator

open Batteries
open Collimator.Core
open Collimator.Concrete

universe u

/--
Construct a traversal from a polymorphic walker that works for any applicative.

A traversal focuses on zero or more parts of a structure, allowing you to
view all of them, modify all of them, or apply effectful transformations.

## Parameters
- `walk`: A function that applies an effectful transformation `(a → F b)` to all
  focused elements in the structure, threading the applicative effect `F` through.

## Example

```lean
-- Traversal over all elements of a list
def listTraversal : Traversal' (List α) α :=
  traversal fun {F} [Applicative F] f xs =>
    let rec go : List α → F (List α)
      | [] => pure []
      | x :: rest => (· :: ·) <$> f x <*> go rest
    go xs

-- Usage:
let nums := [1, 2, 3, 4]

-- Modify all elements
over listTraversal (· * 2) nums  -- [2, 4, 6, 8]

-- Collect all elements
Fold.toListTraversal listTraversal nums  -- [1, 2, 3, 4]

-- Effectful traversal (e.g., validation)
Traversal.traverse' listTraversal
  (fun n => if n > 0 then some n else none)
  nums  -- some [1, 2, 3, 4]

Traversal.traverse' listTraversal
  (fun n => if n > 0 then some n else none)
  [1, -2, 3]  -- none (short-circuits on first failure)
```

## Laws

A lawful traversal satisfies:
1. **Identity**: `traverse id = id` - traversing with identity is a no-op
2. **Composition**: `traverse (Compose . fmap g . f) = Compose . fmap (traverse g) . traverse f`

These laws ensure the traversal visits each element exactly once in a consistent order.
-/
def traversal {s t a b : Type _}
    (walk : ∀ {F : Type u → Type u} [Applicative F], (a → F b) → s → F t) :
    Traversal s t a b :=
  fun {P} [Profunctor P] [Strong P] [Choice P] w pab =>
    let _ : Wandering P := w
    Wandering.wander (P := P) walk pab

private def traverseList {F : Type _ → Type _} [Applicative F]
    {α β : Type u} (f : α → F β) : List α → F (List β)
  | [] => pure []
  | x :: xs => pure List.cons <*> f x <*> traverseList f xs

private def traverseOption {F : Type _ → Type _} [Applicative F]
    {α β : Type u} (f : α → F β) : Option α → F (Option β)
  | none => pure none
  | some a => Option.some <$> f a

namespace Traversal

/-- Modify each focus of a traversal. -/
def over' {s t a b : Type _}
    (tr : Collimator.Traversal s t a b) (f : a → b) : s → t :=
  let arrow := FunArrow.mk (α := a) (β := b) f
  let transformed := tr.toTraversal (P := fun α β => FunArrow α β) inferInstance arrow
  fun s => transformed s

/-- Apply an effectful update to each focus of a traversal. -/
def traverse' {s t a b : Type _}
    (tr : Collimator.Traversal s t a b)
    {F : Type u → Type u} [Applicative F]
    (f : a → F b) (s₀ : s) : F t :=
  let star := Star.mk (F := F) (α := a) (β := b) f
  let transformed := tr.toTraversal (P := fun α β => Star F α β) inferInstance star
  transformed s₀

/-- Traversal focusing every element of a list. -/
def eachList {α β : Type _} :
    Collimator.Traversal (List α) (List β) α β :=
  Collimator.traversal traverseList

/-- Traversal focusing the value inside an `Option` when present. -/
def eachOption {α β : Type _} :
    Collimator.Traversal (Option α) (Option β) α β :=
  Collimator.traversal traverseOption

end Traversal


end Collimator
