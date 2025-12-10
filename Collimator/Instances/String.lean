import Collimator.Optics.Lens
import Collimator.Optics.Traversal
import Collimator.Optics.Iso
import Collimator.Combinators.Indexed

/-!
# String Optics

Optics for working with String as a sequence of characters.

## Key Optics

- `chars` - Iso between String and List Char
- `traversed` - Traverse all characters in a string
- `itraversed` - Indexed traversal with character positions
- `HasAt`/`HasIx` instances for character access by index
-/

namespace Collimator.Instances.String

open Collimator
open Collimator.Indexed

universe u

/-- Isomorphism between String and List Char. -/
@[inline] def chars : Iso' String (List Char) :=
  iso (forward := String.toList) (back := String.mk)

/-- Traversal visiting every character in a string. -/
@[inline] def traversed : Traversal' String Char :=
  Collimator.traversal
    (fun {F : Type → Type} [Applicative F]
      (f : Char → F Char) (s : String) =>
        Functor.map String.mk (List.traverse f s.toList))

/-- Indexed traversal exposing position alongside each character. -/
@[inline] def itraversed : Traversal' String (Nat × Char) :=
  Collimator.traversal
    (fun {F : Type → Type} [Applicative F]
      (f : (Nat × Char) → F (Nat × Char)) (s : String) =>
        let rec helper : Nat → List Char → F (List Char)
        | _, [] => pure []
        | idx, c :: rest =>
            let head := f (idx, c)
            pure List.cons
              <*> Functor.map (fun pair : Nat × Char => pair.2) head
              <*> helper (idx + 1) rest
        Functor.map String.mk (helper 0 s.toList))

private def setCharAt (s : String) (idx : Nat) (replacement : Option Char) : String :=
  let chars := s.toList
  let newChars := match chars.get? idx, replacement with
    | some _, some c => chars.set idx c
    | _, _ => chars  -- No change if index invalid or no replacement
  String.mk newChars

/-- Lens exposing a possibly missing character at a given index. -/
instance instHasAtString : HasAt Nat String Char where
  focus i := lens' (fun s => s.toList.get? i) (fun s r? => setCharAt s i r?)

/-- Traversal focusing the character at a specific index when present. -/
instance instHasIxString : HasIx Nat String Char where
  ix target :=
    Collimator.traversal
      (fun {F : Type → Type} [Applicative F]
        (f : Char → F Char) (s : String) =>
          let rec helper : Nat → List Char → F (List Char)
          | _, [] => pure []
          | idx, c :: rest =>
              if idx == target then
                pure List.cons <*> f c <*> helper (idx + 1) rest
              else
                pure List.cons <*> pure c <*> helper (idx + 1) rest
          Functor.map String.mk (helper 0 s.toList))

end Collimator.Instances.String
