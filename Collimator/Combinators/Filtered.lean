import Collimator.Optics.Types
import Collimator.Optics.Traversal

namespace Collimator.Combinators

open Collimator
open Collimator.Traversal


/--
Restrict a traversal to focuses that satisfy a predicate. The traversal is
monomorphic because the predicate must be evaluated on both the input and the
output type.
-/
def filtered {s : Type} {a : Type}
    (tr : Traversal' s a) (pred : a → Bool) : Traversal' s a :=
  Collimator.traversal
    (fun {F : Type → Type} [Applicative F]
      (f : a → F a) (s₀ : s) =>
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
def filteredList {a : Type} (pred : a → Bool) : Traversal' (List a) a :=
  Collimator.traversal
    (fun {F : Type → Type} [Applicative F]
      (f : a → F a) (xs : List a) =>
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
def ifilteredList {a : Type} (pred : Nat → a → Bool) : Traversal' (List a) a :=
  Collimator.traversal
    (fun {F : Type → Type} [Applicative F]
      (f : a → F a) (xs : List a) =>
        let rec go : Nat → List a → F (List a)
          | _, [] => pure []
          | idx, x :: rest =>
              if pred idx x then
                (· :: ·) <$> f x <*> go (idx + 1) rest
              else
                (x :: ·) <$> go (idx + 1) rest
        go 0 xs)

end Collimator.Combinators
