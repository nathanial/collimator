import Collimator.Optics.Types
import Collimator.Optics.Affine
import Collimator.Optics.Traversal
import Collimator.Core.Strong
import Collimator.Core.Choice

/-!
# Safe List Operations

Optics for safely accessing elements of lists without risking runtime errors.
-/

namespace Collimator.Combinators

open Collimator
open Collimator.Core

universe u

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
def _head {a : Type u} : AffineTraversal' (List a) a :=
  ⟨fun {P} [Profunctor P] hStrong hChoice pab =>
    let _ : Strong P := hStrong
    let _ : Choice P := hChoice
    -- Split list into Either [] (head, tail)
    Profunctor.dimap
      (fun xs : List a => match xs with
        | [] => Sum.inl []
        | x :: rest => Sum.inr (x, rest))
      (fun
        | Sum.inl xs => xs
        | Sum.inr (x, rest) => x :: rest)
      (Choice.right (Strong.first pab))⟩

/--
Safely access the last element of a list.

Returns `AffineTraversal` because the list may be empty.

```lean
preview _last [1, 2, 3]  -- some 3
preview _last []         -- none
over _last (· * 10) [1, 2, 3]  -- [1, 2, 30]
```
-/
def _last {a : Type u} : AffineTraversal' (List a) a :=
  ⟨fun {P} [Profunctor P] hStrong hChoice pab =>
    let _ : Strong P := hStrong
    let _ : Choice P := hChoice
    -- Split list into Either [] (init, last)
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
      (Choice.right (Strong.second pab))⟩

/--
Traverse the first `n` elements of a list.

Elements beyond the first `n` are left unchanged.

```lean
over (taking 2) (· * 10) [1, 2, 3, 4]  -- [10, 20, 3, 4]
over (taking 0) (· * 10) [1, 2, 3]     -- [1, 2, 3]
over (taking 10) (· * 10) [1, 2]       -- [10, 20]
```
-/
def taking {a : Type u} (n : Nat) : Traversal' (List a) a :=
  Collimator.traversal
    (fun {F : Type u → Type u} [Applicative F]
      (f : a → F a) (xs : List a) =>
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
def dropping {a : Type u} (n : Nat) : Traversal' (List a) a :=
  Collimator.traversal
    (fun {F : Type u → Type u} [Applicative F]
      (f : a → F a) (xs : List a) =>
        let (prefix_, suffix) := xs.splitAt n
        let rec traverseList : List a → F (List a)
          | [] => pure []
          | x :: rest => (· :: ·) <$> f x <*> traverseList rest
        (prefix_ ++ ·) <$> traverseList suffix)

end Collimator.Combinators
