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
