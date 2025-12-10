import Batteries
import Collimator.Optics
import Collimator.Combinators

namespace Collimator.Instances.List

open Batteries
open Collimator
open Collimator.Indexed


/-- Traversal visiting every element of a list. -/
@[inline] def traversed {α β : Type} :
    Traversal (List α) (List β) α β :=
  Collimator.Traversal.eachList

/-- Indexed traversal exposing the list index alongside each element. -/
@[inline] def itraversed {α : Type} :
    Traversal' (List α) (Nat × α) :=
  Collimator.traversal
    (fun {F : Type → Type} [Applicative F]
      (f : (Nat × α) → F (Nat × α)) (xs : List α) =>
        let rec helper : Nat → List α → F (List α)
        | _, [] => pure []
        | idx, x :: rest =>
            let head := f (idx, x)
            pure List.cons
              <*> Functor.map (fun pair : Nat × α => pair.2) head
              <*> helper (idx + 1) rest
        helper 0 xs)

private def setAt?
    {α : Type} (xs : List α) (idx : Nat) (replacement : Option α) : List α :=
  match xs, idx, replacement with
  | [], _, _ => []
  | _ :: rest, 0, some v => v :: rest
  | x :: rest, 0, none => x :: rest
  | x :: rest, Nat.succ i, r? => x :: setAt? rest i r?

/-- Lens exposing a possibly missing element of a list at a given index. -/
instance instHasAtList {α : Type} : HasAt Nat (List α) α where
  focus i :=
    lens' (fun xs => xs[i]? ) (fun xs r? => setAt? xs i r?)

/-- Traversal focusing the element at a specific index when present. -/
instance instHasIxList {α : Type} : HasIx Nat (List α) α where
  ix target :=
    Collimator.traversal
      (fun {F : Type → Type} [Applicative F]
        (f : α → F α) (xs : List α) =>
          let rec helper : Nat → List α → F (List α)
          | _, [] => pure []
          | idx, x :: rest =>
              if idx == target then
                pure List.cons <*> f x <*> helper (idx + 1) rest
              else
                pure List.cons <*> pure x <*> helper (idx + 1) rest
          helper 0 xs)

end Collimator.Instances.List
