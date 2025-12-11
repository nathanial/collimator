import Collimator.Core
import Collimator.Optics
import Collimator.Concrete.Star
import Collimator.Combinators

/-!
# Traversal Laws

This module formalizes and proves the fundamental traversal laws for profunctor optics:
1. **Identity**: Traversing with pure gives back pure of the structure
2. **Composition**: Traversals compose properly with applicative functors

## References
- Profunctor Optics: Modular Data Accessors (Pickering, Gibbons, Wu)
- The Essence of the Iterator Pattern (Gibbons, Oliveira)
- ProfunctorOpticsDesign.md Phase 5
-/

namespace Collimator.Theorems

open Collimator
open Collimator.Core
open Collimator.Concrete


/--
The identity functor - maps values to themselves.
-/
abbrev Id (α : Type) : Type := α

instance : Functor Id where
  map f := f

instance : Applicative Id where
  pure a := a
  seq f x := f (x ())

/--
A lawful traversal requires the underlying walk function to satisfy two laws.

Note: For the polymorphic case where s≠t or a≠b, we state the laws in terms
of the monomorphic version where we restrict to s=t and a=b.
-/
class LawfulTraversal {s : Type} {a : Type}
    (walk : ∀ {F : Type → Type} [Applicative F], (a → F a) → s → F s) where
  /-- Traversing with the identity function returns the structure unchanged (identity law). -/
  traverse_identity : ∀ (x : s), walk (F := Id) (fun a => a) x = x
  /-- The naturality law: walk commutes with natural transformations. -/
  traverse_naturality :
    ∀ {F G : Type → Type} [Applicative F] [Applicative G]
      (η : ∀ {α}, F α → G α)
      (_h_pure : ∀ {α} (a : α), η (pure a : F α) = pure a)
      (_h_seq : ∀ {α β} (f : F (α → β)) (x : F α),
        η (f <*> x) = η f <*> η x)
      (f : a → F a) (x : s),
    η (walk f x) = walk (fun a => η (f a)) x

/-! ## Helper Lemmas -/

/--
Unfolding lemma: `Traversal.over` applied to a traversal.
-/
theorem traversal_over_eq {s a : Type}
    (walk : ∀ {F : Type → Type} [Applicative F], (a → F a) → s → F s)
    (f : a → a) (x : s) :
    Traversal.over' (traversal walk) f x = walk (F := Id) f x := by
  unfold Traversal.over' traversal Wandering.wander
  simp only []
  rfl

/--
Unfolding lemma: `Traversal.traverse` applied to a traversal.
-/
theorem traversal_traverse_eq {s a : Type}
    (walk : ∀ {F : Type → Type} [Applicative F], (a → F a) → s → F s)
    {F : Type → Type} [Applicative F]
    (f : a → F a) (x : s) :
    Traversal.traverse' (traversal walk) f x = walk (F := F) f x := by
  unfold Traversal.traverse' traversal Wandering.wander
  simp only []
  rfl

/-! ## Main Traversal Laws -/

/--
**Identity Law**: Traversing over a structure with the identity function
leaves the structure unchanged.

If `t = traversal walk` and the walk function satisfies the identity law,
then `Traversal.over t id x = x`.
-/
theorem traversal_identity {s a : Type}
    (walk : ∀ {F : Type → Type} [Applicative F], (a → F a) → s → F s)
    (h : ∀ (x : s), walk (F := Id) (fun a => a) x = x) :
    ∀ (x : s), Traversal.over' (traversal walk) (fun a => a) x = x := by
  intro x
  rw [traversal_over_eq]
  exact h x

/--
**Naturality Law**: Traversals respect natural transformations between applicatives.
-/
theorem traversal_naturality {s a : Type}
    (walk : ∀ {F : Type → Type} [Applicative F], (a → F a) → s → F s)
    (h : ∀ {F G : Type → Type} [Applicative F] [Applicative G]
      (η : ∀ {α}, F α → G α)
      (_h_pure : ∀ {α} (a : α), η (pure a : F α) = pure a)
      (_h_seq : ∀ {α β} (f : F (α → β)) (x : F α), η (f <*> x) = η f <*> η x)
      (f : a → F a) (x : s),
      η (walk f x) = walk (fun a => η (f a)) x) :
    ∀ {F G : Type → Type} [Applicative F] [Applicative G]
      (η : ∀ {α}, F α → G α)
      (_h_pure : ∀ {α} (a : α), η (pure a : F α) = pure a)
      (_h_seq : ∀ {α β} (f : F (α → β)) (x : F α), η (f <*> x) = η f <*> η x)
      (f : a → F a) (x : s),
    η (Traversal.traverse' (traversal walk) f x) =
      Traversal.traverse' (traversal walk) (fun a => η (f a)) x := by
  intro F G _ _ η _h_pure _h_seq f x
  rw [traversal_traverse_eq, traversal_traverse_eq]
  exact h η _h_pure _h_seq f x

/-! ## Bundled Lawful Traversal Theorems -/

/--
If the underlying walk function forms a lawful traversal, then both traversal laws hold
for the profunctor traversal constructed from it.
-/
theorem lawful_traversal_satisfies_laws {s a : Type}
    (walk : ∀ {F : Type → Type} [Applicative F], (a → F a) → s → F s)
    [h : LawfulTraversal walk] :
    (∀ (x : s), Traversal.over' (traversal walk) (fun a => a) x = x) ∧
    (∀ {F G : Type → Type} [Applicative F] [Applicative G]
      (η : ∀ {α}, F α → G α)
      (_h_pure : ∀ {α} (a : α), η (pure a : F α) = pure a)
      (_h_seq : ∀ {α β} (f : F (α → β)) (x : F α), η (f <*> x) = η f <*> η x)
      (f : a → F a) (x : s),
      η (Traversal.traverse' (traversal walk) f x) =
        Traversal.traverse' (traversal walk) (fun a => η (f a)) x) := by
  constructor
  · exact traversal_identity walk h.traverse_identity
  · intro F G _ _ η h_pure h_seq f x
    exact traversal_naturality walk h.traverse_naturality η h_pure h_seq f x

/-! ## Traversal Composition Laws -/

open Collimator.Combinators

/--
Helper: Extract walker from composed traversals.
-/
private def composed_walk {s u a : Type}
    (walk_outer : ∀ {F : Type → Type} [Applicative F], (u → F u) → s → F s)
    (walk_inner : ∀ {F : Type → Type} [Applicative F], (a → F a) → u → F u) :
    ∀ {F : Type → Type} [Applicative F], (a → F a) → s → F s :=
  fun {F} [Applicative F] f => walk_outer (walk_inner f)

/--
**Composition Preserves Identity**: If two traversals are lawful,
their composition preserves the identity law.
-/
theorem composeTraversal_preserves_identity {s u a : Type}
    (walk_o : ∀ {F : Type → Type} [Applicative F], (u → F u) → s → F s)
    (walk_i : ∀ {F : Type → Type} [Applicative F], (a → F a) → u → F u)
    [ho : LawfulTraversal walk_o] [hi : LawfulTraversal walk_i] :
    ∀ (x : s), composed_walk walk_o walk_i (F := Id) (fun a => a) x = x := by
  intro x
  unfold composed_walk
  have h1 : (fun u => walk_i (F := Id) (fun a => a) u) = fun u => u := by
    funext u
    exact hi.traverse_identity u
  simp only [h1]
  exact ho.traverse_identity x

/--
**Composition Preserves Naturality**: If two traversals are lawful,
their composition preserves the naturality law.
-/
theorem composeTraversal_preserves_naturality {s u a : Type}
    (walk_o : ∀ {F : Type → Type} [Applicative F], (u → F u) → s → F s)
    (walk_i : ∀ {F : Type → Type} [Applicative F], (a → F a) → u → F u)
    [ho : LawfulTraversal walk_o] [hi : LawfulTraversal walk_i] :
    ∀ {F G : Type → Type} [Applicative F] [Applicative G]
      (η : ∀ {α}, F α → G α)
      (_h_pure : ∀ {α} (a : α), η (pure a : F α) = pure a)
      (_h_seq : ∀ {α β} (f : F (α → β)) (x : F α), η (f <*> x) = η f <*> η x)
      (f : a → F a) (x : s),
    η (composed_walk walk_o walk_i f x) =
      composed_walk walk_o walk_i (fun a => η (f a)) x := by
  intro F G _ _ η h_pure h_seq f x
  unfold composed_walk
  rw [ho.traverse_naturality (fun x => η x) h_pure h_seq]
  congr
  funext y
  exact hi.traverse_naturality η h_pure h_seq f y

/--
**Composition is Lawful**: If two traversals are lawful, their composition is lawful.
-/
instance composedTraversal_isLawful {s u a : Type}
    (walk_o : ∀ {F : Type → Type} [Applicative F], (u → F u) → s → F s)
    (walk_i : ∀ {F : Type → Type} [Applicative F], (a → F a) → u → F u)
    [ho : LawfulTraversal walk_o] [hi : LawfulTraversal walk_i] :
    LawfulTraversal (composed_walk walk_o walk_i) where
  traverse_identity := composeTraversal_preserves_identity walk_o walk_i
  traverse_naturality := composeTraversal_preserves_naturality walk_o walk_i

/-! ## Examples -/

/--
Example: List traversal is lawful.
-/
private def traverseList'Mon {α : Type} {F : Type → Type} [Applicative F]
    (f : α → F α) : List α → F (List α)
  | [] => pure []
  | x :: xs => pure List.cons <*> f x <*> traverseList'Mon f xs

instance {α : Type} : LawfulTraversal (@traverseList'Mon α) where
  traverse_identity := by
    intro x
    induction x with
    | nil => rfl
    | cons h t ih =>
      unfold traverseList'Mon
      simp only [ih]
      rfl
  traverse_naturality := by
    intro F G _ _ η h_pure h_seq f x
    induction x with
    | nil =>
      unfold traverseList'Mon
      simp only [h_pure]
    | cons h t ih =>
      unfold traverseList'Mon
      rw [h_seq, h_seq, ih]
      simp only [h_pure]

/--
Example: Option traversal is lawful.

Note: We use a direct encoding with applicative operations instead of (<$>)
to make the naturality proof simpler.
-/
private def traverseOption'Mon {α : Type} {F : Type → Type} [Applicative F]
    (f : α → F α) : Option α → F (Option α)
  | none => pure none
  | some a => pure Option.some <*> f a

instance {α : Type} : LawfulTraversal (@traverseOption'Mon α) where
  traverse_identity := by
    intro x
    cases x <;> rfl
  traverse_naturality := by
    intro F G _ _ η h_pure h_seq f x
    cases x with
    | none =>
      unfold traverseOption'Mon
      simp only [h_pure]
    | some a =>
      unfold traverseOption'Mon
      rw [h_seq, h_pure]

end Collimator.Theorems
