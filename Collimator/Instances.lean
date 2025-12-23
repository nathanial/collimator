import Batteries
import Collimator.Optics
import Collimator.Combinators

/-!
# Type Instances for Collimator Optics

This module provides optic instances for common Lean types:
- Array: traversed, itraversed, HasAt, HasIx
- AssocList: HasAt, HasIx (key-based access)
- HashMap: HasAt, HasIx (key-based access)
- List: traversed, itraversed, HasAt, HasIx
- Option: somePrism, HasAt
- Prod: first, second, and nested tuple accessors
- String: chars iso, traversed, itraversed, HasAt, HasIx
- Sum: left and right prisms
-/

namespace Collimator.Instances

open Batteries
open Collimator
open Collimator.Indexed
open Collimator.Core
open Collimator.Combinators

/-! ## Array Instances -/
namespace Array

private def traverseArray
    {F : Type → Type} [Applicative F]
    {α β : Type} (f : α → F β) (arr : Array α) : F (Array β) :=
  let step (acc : F (Array β)) (a : α) : F (Array β) :=
    pure (fun (accArr : Array β) (b : β) => accArr.push b) <*> acc <*> f a
  arr.foldl step (pure (_root_.Array.mkEmpty (α := β) arr.size))

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
  (arr.foldl step (0, pure (_root_.Array.mkEmpty (α := α) arr.size))).2

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
          (arr.foldl step (0, pure (_root_.Array.mkEmpty (α := α) arr.size))).2)

end Array

/-! ## List Instances -/
namespace List

/-- Traversal visiting every element of a list. -/
@[inline] def traversed {α β : Type} :
    Traversal (_root_.List α) (_root_.List β) α β :=
  Collimator.Traversal.eachList

/-- Indexed traversal exposing the list index alongside each element. -/
@[inline] def itraversed {α : Type} :
    Traversal' (_root_.List α) (Nat × α) :=
  Collimator.traversal
    (fun {F : Type → Type} [Applicative F]
      (f : (Nat × α) → F (Nat × α)) (xs : _root_.List α) =>
        let rec helper : Nat → _root_.List α → F (_root_.List α)
        | _, [] => pure []
        | idx, x :: rest =>
            let head := f (idx, x)
            pure _root_.List.cons
              <*> Functor.map (fun pair : Nat × α => pair.2) head
              <*> helper (idx + 1) rest
        helper 0 xs)

private def setAt?
    {α : Type} (xs : _root_.List α) (idx : Nat) (replacement : Option α) : _root_.List α :=
  match xs, idx, replacement with
  | [], _, _ => []
  | _ :: rest, 0, some v => v :: rest
  | x :: rest, 0, none => x :: rest
  | x :: rest, Nat.succ i, r? => x :: setAt? rest i r?

/-- Lens exposing a possibly missing element of a list at a given index. -/
instance instHasAtList {α : Type} : HasAt Nat (_root_.List α) α where
  focus i :=
    lens' (fun xs => xs[i]? ) (fun xs r? => setAt? xs i r?)

/-- Traversal focusing the element at a specific index when present. -/
instance instHasIxList {α : Type} : HasIx Nat (_root_.List α) α where
  ix target :=
    Collimator.traversal
      (fun {F : Type → Type} [Applicative F]
        (f : α → F α) (xs : _root_.List α) =>
          let rec helper : Nat → _root_.List α → F (_root_.List α)
          | _, [] => pure []
          | idx, x :: rest =>
              if idx == target then
                pure _root_.List.cons <*> f x <*> helper (idx + 1) rest
              else
                pure _root_.List.cons <*> pure x <*> helper (idx + 1) rest
          helper 0 xs)

end List

/-! ## Option Instances -/
namespace Option

/-- Prism focusing the value of an option when present (polymorphic version). -/
@[inline] def somePrism {α β : Type} : Prism (_root_.Option α) (_root_.Option β) α β :=
  fun {P} [Profunctor P] hChoice pab =>
    let _ : Choice P := hChoice
    let right := Choice.right (P := P) (γ := _root_.Option β) pab
    let split : _root_.Option α → Sum (_root_.Option β) α :=
      fun s => match s with
        | .some a => Sum.inr a
        | .none => Sum.inl (_root_.Option.none : _root_.Option β)
    let post : Sum (_root_.Option β) β → _root_.Option β :=
      fun s => match s with
        | Sum.inl opt => opt
        | Sum.inr b => _root_.Option.some b
    Profunctor.dimap (P := P) split post right

/-- Monomorphic version of somePrism for easier use in compositions.

Usage in compositions:
```lean
-- Clean syntax with monomorphic version
ofPrism (somePrism' Employee)

-- vs polymorphic version requiring both type parameters
ofPrism (somePrism (α := Employee) (β := Employee))
```
-/
@[inline] def somePrism' (α : Type) : Prism' (_root_.Option α) α :=
  somePrism

instance instHasAtOption {α : Type} : HasAt Unit (_root_.Option α) α where
  focus _ :=
    lens' (fun o => o) (fun _ replacement => replacement)

end Option

/-! ## Prod Instances -/
namespace Prod

/-- Lens focusing the first component of a pair. -/
@[inline] def first {α β γ : Type} :
    Lens (α × β) (γ × β) α γ :=
  _1

/-- Lens focusing the second component of a pair. -/
@[inline] def second {α β γ : Type} :
    Lens (α × β) (α × γ) β γ :=
  _2

/-- Lens focusing the first element of a triple represented as nested pairs. -/
@[inline] def firstOfTriple {α β γ δ : Type} :
    Lens ((α × β) × γ) ((δ × β) × γ) α δ :=
  _1 ∘ _1

/-- Lens focusing the middle element of a triple represented as nested pairs. -/
@[inline] def secondOfTriple {α β γ δ : Type} :
    Lens ((α × β) × γ) ((α × δ) × γ) β δ :=
  _1 ∘ _2

/-- Lens focusing the final element of a triple represented as nested pairs. -/
@[inline] def thirdOfTriple {α β γ δ : Type} :
    Lens ((α × β) × γ) ((α × β) × δ) γ δ :=
  _2

end Prod

/-! ## String Instances -/
namespace String

/-- Isomorphism between String and List Char. -/
@[inline] def chars : Iso' _root_.String (_root_.List Char) :=
  iso (forward := _root_.String.toList) (back := _root_.String.ofList)

/-- Traversal visiting every character in a string. -/
@[inline] def traversed : Traversal' _root_.String Char :=
  Collimator.traversal
    (fun {F : Type → Type} [Applicative F]
      (f : Char → F Char) (s : _root_.String) =>
        Functor.map _root_.String.ofList (_root_.List.traverse f s.toList))

/-- Indexed traversal exposing position alongside each character. -/
@[inline] def itraversed : Traversal' _root_.String (Nat × Char) :=
  Collimator.traversal
    (fun {F : Type → Type} [Applicative F]
      (f : (Nat × Char) → F (Nat × Char)) (s : _root_.String) =>
        let rec helper : Nat → _root_.List Char → F (_root_.List Char)
        | _, [] => pure []
        | idx, c :: rest =>
            let head := f (idx, c)
            pure _root_.List.cons
              <*> Functor.map (fun pair : Nat × Char => pair.2) head
              <*> helper (idx + 1) rest
        Functor.map _root_.String.ofList (helper 0 s.toList))

private def setCharAt (s : _root_.String) (idx : Nat) (replacement : _root_.Option Char) : _root_.String :=
  let chars := s.toList
  let newChars := match chars[idx]?, replacement with
    | some _, some c => chars.set idx c
    | _, _ => chars  -- No change if index invalid or no replacement
  _root_.String.ofList newChars

/-- Lens exposing a possibly missing character at a given index. -/
instance instHasAtString : HasAt Nat _root_.String Char where
  focus i := lens' (fun s => s.toList[i]?) (fun s r? => setCharAt s i r?)

/-- Traversal focusing the character at a specific index when present. -/
instance instHasIxString : HasIx Nat _root_.String Char where
  ix target :=
    Collimator.traversal
      (fun {F : Type → Type} [Applicative F]
        (f : Char → F Char) (s : _root_.String) =>
          let rec helper : Nat → _root_.List Char → F (_root_.List Char)
          | _, [] => pure []
          | idx, c :: rest =>
              if idx == target then
                pure _root_.List.cons <*> f c <*> helper (idx + 1) rest
              else
                pure _root_.List.cons <*> pure c <*> helper (idx + 1) rest
          Functor.map _root_.String.ofList (helper 0 s.toList))

end String

/-! ## Sum Instances -/
namespace Sum

/-- Prism focusing the left branch of a sum (polymorphic version). -/
@[inline] def left {α β γ : Type} :
    Prism (_root_.Sum α β) (_root_.Sum γ β) α γ :=
  prism (s := _root_.Sum α β) (t := _root_.Sum γ β) (a := α) (b := γ)
    (build := _root_.Sum.inl)
    (split :=
      fun
      | _root_.Sum.inl a => _root_.Sum.inr a
      | _root_.Sum.inr b => _root_.Sum.inl (_root_.Sum.inr b))

/-- Monomorphic version of left prism for easier use in compositions.

Usage in compositions:
```lean
-- Clean syntax with monomorphic version
left' String Employee

-- vs polymorphic version requiring all type parameters
left (α := String) (β := Employee) (γ := String)
```
-/
@[inline] def left' (α β : Type) : Prism' (_root_.Sum α β) α := left

/-- Prism focusing the right branch of a sum (polymorphic version). -/
@[inline] def right {α β γ : Type} :
    Prism (_root_.Sum α β) (_root_.Sum α γ) β γ :=
  prism (s := _root_.Sum α β) (t := _root_.Sum α γ) (a := β) (b := γ)
    (build := _root_.Sum.inr)
    (split :=
      fun
      | _root_.Sum.inr b => _root_.Sum.inr b
      | _root_.Sum.inl a => _root_.Sum.inl (_root_.Sum.inl a))

/-- Monomorphic version of right prism for easier use in compositions.

Usage in compositions:
```lean
-- Clean syntax with monomorphic version
right' String Employee

-- vs polymorphic version requiring all type parameters
right (α := String) (β := Employee) (γ := Employee)
```
-/
@[inline] def right' (α β : Type) : Prism' (_root_.Sum α β) β := right

end Sum

/-! ## HashMap Instances -/
namespace HashMap

variable {k v : Type} [BEq k] [Hashable k]

/-- Lens exposing an optional value at a given key in a HashMap. -/
instance instHasAtHashMap : HasAt k (Std.HashMap k v) v where
  focus key :=
    lens'
      (fun m => m.get? key)
      (fun m r? => match r? with
        | some val => m.insert key val
        | none => m.erase key)

/-- Traversal focusing the value at a specific key when present. -/
instance instHasIxHashMap : HasIx k (Std.HashMap k v) v where
  ix key :=
    Collimator.traversal
      (fun {F : Type → Type} [Applicative F] (f : v → F v) (m : Std.HashMap k v) =>
        match m.get? key with
        | some val => Functor.map (fun v' => m.insert key v') (f val)
        | none => pure m)

end HashMap

/-! ## AssocList Instances -/
namespace AssocList

variable {k v : Type} [BEq k]

/-- Insert or update a key-value pair (avoids double lookup). -/
private def upsert (xs : AssocList k v) (key : k) (val : v) : AssocList k v :=
  match xs.find? key with
  | some _ => xs.replace key val
  | none => AssocList.cons key val xs

private def setAt? (xs : AssocList k v) (key : k) (r? : Option v) : AssocList k v :=
  match r? with
  | some val => upsert xs key val
  | none => xs.erase key

/-- Lens exposing an optional value at a given key in an AssocList. -/
instance instHasAtAssocList : HasAt k (AssocList k v) v where
  focus key :=
    lens'
      (fun xs => xs.find? key)
      (fun xs r? => setAt? xs key r?)

/-- Traversal focusing the value at a specific key when present. -/
instance instHasIxAssocList : HasIx k (AssocList k v) v where
  ix key :=
    Collimator.traversal
      (fun {F : Type → Type} [Applicative F] (f : v → F v) (xs : AssocList k v) =>
        match xs.find? key with
        | some val => Functor.map (fun v' => xs.replace key v') (f val)
        | none => pure xs)

end AssocList

end Collimator.Instances
