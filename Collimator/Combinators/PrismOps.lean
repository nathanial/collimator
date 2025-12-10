import Collimator.Optics.Types
import Collimator.Optics.Prism
import Collimator.Optics.Affine
import Collimator.Core.Strong
import Collimator.Core.Choice

/-!
# Prism Combinators

Additional operations for working with prisms.
-/

namespace Collimator.Combinators

open Collimator
open Collimator.Core

universe u

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
def orElse {s a : Type u}
    (p1 : Prism' s a) (p2 : Prism' s a) : AffineTraversal' s a :=
  ⟨fun {P} [Profunctor P] hStrong hChoice pab =>
    let _ : Strong P := hStrong
    let _ : Choice P := hChoice
    -- Try p1 first, if Sum.inl (failed), try p2
    -- This requires constructing the affine traversal manually
    let tryBoth : s → Sum s (a × s) := fun s =>
      match preview' p1 s with
      | some a => Sum.inr (a, s)
      | none => match preview' p2 s with
        | some a => Sum.inr (a, s)
        | none => Sum.inl s
    -- Build the affine traversal
    Profunctor.dimap
      tryBoth
      (fun
        | Sum.inl s => s
        | Sum.inr (a, origS) =>
          -- Determine which prism matched and use appropriate modification
          match preview' p1 origS with
          | some _ => review' p1 a
          | none => review' p2 a)
      (Choice.right (Strong.first pab))⟩

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
def affineFromPartial {s a : Type u}
    (preview_ : s → Option a)
    (set_ : s → a → s) : AffineTraversal' s a :=
  ⟨fun {P} [Profunctor P] hStrong hChoice pab =>
    let _ : Strong P := hStrong
    let _ : Choice P := hChoice
    Profunctor.dimap
      (fun s => match preview_ s with
        | some a => Sum.inr (a, s)
        | none => Sum.inl s)
      (fun
        | Sum.inl s => s
        | Sum.inr (a, s) => set_ s a)
      (Choice.right (Strong.first pab))⟩

end Collimator.Combinators
