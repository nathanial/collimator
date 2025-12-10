import Batteries
import Collimator.Optics.Lens
import Collimator.Optics.Traversal
import Collimator.Combinators.Indexed

namespace Collimator.Instances.Array

open Batteries
open Collimator
open Collimator.Indexed


private def traverseArray
    {F : Type → Type} [Applicative F]
    {α β : Type} (f : α → F β) (arr : Array α) : F (Array β) :=
  let step (acc : F (Array β)) (a : α) : F (Array β) :=
    pure (fun (accArr : Array β) (b : β) => accArr.push b) <*> acc <*> f a
  arr.foldl step (pure (Array.mkEmpty (α := β) arr.size))

private def traverseArrayWithIndex
    {F : Type → Type} [Applicative F]
    {α : Type}
    (f : Nat × α → F (Nat × α)) (arr : Array α) : F (Array α) :=
  let step
      (state : Nat × F (Array α)) (a : α) : Nat × F (Array α) :=
    let idx := state.fst
    let acc := state.snd
    let updated :=
      pure (fun (accArr : Array α) (pair : Nat × α) => accArr.push pair.2)
        <*> acc <*> f (idx, a)
    (idx + 1, updated)
  (arr.foldl step (0, pure (Array.mkEmpty (α := α) arr.size))).2

private def setAt?
    {α : Type} (arr : Array α) (idx : Nat) (replacement : Option α) : Array α :=
  match replacement with
  | some v =>
      if h : idx < arr.size then
        arr.set idx v (by exact h)
      else
        arr
  | none => arr

/-- Traversal visiting every element of an array. -/
@[inline] def traversed {α β : Type} :
    Traversal (Array α) (Array β) α β :=
  Collimator.traversal
    (fun {F : Type → Type} [Applicative F]
      (f : α → F β) (arr : Array α) =>
        traverseArray f arr)

/-- Indexed traversal exposing array indices alongside each element. -/
@[inline] def itraversed {α : Type} :
    Traversal' (Array α) (Nat × α) :=
  Collimator.traversal
    (fun {F : Type → Type} [Applicative F]
      (f : (Nat × α) → F (Nat × α)) (arr : Array α) =>
        traverseArrayWithIndex f arr)

/-- Lens exposing an optional element at a given array index. -/
instance instHasAtArray {α : Type} : HasAt Nat (Array α) α where
  focus i :=
    lens'
      (fun arr => arr[i]? )
      (fun arr r? => setAt? arr i r?)

/-- Traversal focusing a specific array index when present. -/
instance instHasIxArray {α : Type} : HasIx Nat (Array α) α where
  ix target :=
    Collimator.traversal
      (fun {F : Type → Type} [Applicative F]
        (f : α → F α) (arr : Array α) =>
          let step
              (state : Nat × F (Array α)) (a : α) : Nat × F (Array α) :=
            let idx := state.fst
            let acc := state.snd
            let next :=
              if idx == target then
                pure (fun (accArr : Array α) (b : α) => accArr.push b) <*> acc <*> f a
              else
                Functor.map (fun (accArr : Array α) => accArr.push a) acc
            (idx + 1, next)
          (arr.foldl step (0, pure (Array.mkEmpty (α := α) arr.size))).2)

end Collimator.Instances.Array
