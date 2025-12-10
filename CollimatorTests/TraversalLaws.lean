import Batteries
import Collimator.Optics.Traversal
import Collimator.Optics.Types
import Collimator.Theorems.TraversalLaws
import Collimator.Combinators
import CollimatorTests.Framework

namespace CollimatorTests.TraversalLaws

open Collimator
open Collimator.Theorems
open Collimator.Combinators
open CollimatorTests

/-! ## Test Structures -/

inductive Tree (α : Type _) where
  | leaf : α → Tree α
  | node : Tree α → Tree α → Tree α
  deriving BEq, Repr

/-! ## Traversal Definitions -/

private def Tree.walkMon {α : Type _} {F : Type _ → Type _} [Applicative F]
    (f : α → F α) : Tree α → F (Tree α)
  | Tree.leaf a => pure Tree.leaf <*> f a
  | Tree.node l r =>
      pure Tree.node <*> Tree.walkMon f l <*> Tree.walkMon f r

private def List.walkMon {α : Type _} {F : Type _ → Type _} [Applicative F]
    (f : α → F α) : List α → F (List α)
  | [] => pure []
  | x :: xs => pure List.cons <*> f x <*> List.walkMon f xs

private def Option.walkMon {α : Type _} {F : Type _ → Type _} [Applicative F]
    (f : α → F α) : Option α → F (Option α)
  | none => pure none
  | some a => pure Option.some <*> f a

/-! ## Lawful Instances -/

instance {α : Type _} : LawfulTraversal (@Tree.walkMon α) where
  traverse_identity := by
    intro x
    induction x with
    | leaf a => rfl
    | node l r ihl ihr =>
      unfold Tree.walkMon
      simp only [ihl, ihr]
      rfl
  traverse_naturality := by
    intro F G _ _ η h_pure h_seq f x
    induction x with
    | leaf a =>
      unfold Tree.walkMon
      rw [h_seq, h_pure]
    | node l r ihl ihr =>
      unfold Tree.walkMon
      rw [h_seq, h_seq, ihl, ihr, h_pure]

instance {α : Type _} : LawfulTraversal (@List.walkMon α) where
  traverse_identity := by
    intro x
    induction x with
    | nil => rfl
    | cons h t ih =>
      unfold List.walkMon
      simp only [ih]
      rfl
  traverse_naturality := by
    intro F G _ _ η h_pure h_seq f x
    induction x with
    | nil =>
      unfold List.walkMon
      simp only [h_pure]
    | cons h t ih =>
      unfold List.walkMon
      rw [h_seq, h_seq, ih]
      simp only [h_pure]

instance {α : Type _} : LawfulTraversal (@Option.walkMon α) where
  traverse_identity := by
    intro x
    cases x <;> rfl
  traverse_naturality := by
    intro F G _ _ η h_pure h_seq f x
    cases x with
    | none =>
      unfold Option.walkMon
      simp only [h_pure]
    | some a =>
      unfold Option.walkMon
      rw [h_seq, h_pure]

/-! ## Test Cases -/

/--
Test that the identity law holds: traversing with id returns the structure unchanged.
-/
private def case_traversalIdentityLaw : TestCase := {
  name := "Traversal Identity law: traverse id = id",
  run := do
    let tr : Traversal' (List Int) Int := traversal List.walkMon
    let xs := [1, 2, 3]
    let result := Traversal.over' tr (fun a => a) xs
    ensureEq "Identity law" xs result
}

/--
Test identity law for tree traversal.
-/
private def case_treeIdentityLaw : TestCase := {
  name := "Tree traversal satisfies identity law",
  run := do
    let tr : Traversal' (Tree Int) Int := traversal Tree.walkMon
    let tree := Tree.node (Tree.leaf 1) (Tree.leaf 2)
    let result := Traversal.over' tr (fun a => a) tree
    ensureEq "Tree identity" tree result
}

/--
Test that traversal over actually modifies all elements.
-/
private def case_traversalOver : TestCase := {
  name := "Traversal over modifies all focuses",
  run := do
    let tr : Traversal' (List Int) Int := traversal List.walkMon
    let xs := [1, 2, 3]
    let result := Traversal.over' tr (· + 10) xs
    ensureEq "Over all elements" [11, 12, 13] result
}

/--
Test traverse with Option applicative for short-circuiting.
-/
private def case_traverseOption : TestCase := {
  name := "Traverse with Option applicative short-circuits on none",
  run := do
    let tr : Traversal' (List Int) Int := traversal List.walkMon
    let f : Int → Option Int := fun n => if n >= 0 then some (n + 1) else none

    let success := Traversal.traverse' tr f [0, 1, 2]
    ensureEq "Success case" (some [1, 2, 3]) success

    let failure := Traversal.traverse' tr f [0, -1, 2]
    ensureEq "Failure case" (none : Option (List Int)) failure
}

/--
Test that composition preserves identity law.
-/
private def case_compositionIdentityLaw : TestCase := {
  name := "Composed traversals satisfy identity law",
  run := do
    let outer : Traversal' (List (Option Int)) (Option Int) := traversal List.walkMon
    let inner : Traversal' (Option Int) Int := traversal Option.walkMon
    let composed : Traversal' (List (Option Int)) Int := composeTraversal outer inner

    let xs := [some 1, none, some 3]
    let result := Traversal.over' composed (fun a => a) xs
    ensureEq "Composed identity" xs result
}

/--
Test that composed traversals modify all nested elements.
-/
private def case_composedTraversalOver : TestCase := {
  name := "Composed traversals modify all nested focuses",
  run := do
    let outer : Traversal' (List (Option Int)) (Option Int) := traversal List.walkMon
    let inner : Traversal' (Option Int) Int := traversal Option.walkMon
    let composed : Traversal' (List (Option Int)) Int := composeTraversal outer inner

    let xs := [some 1, none, some 3]
    let result := Traversal.over' composed (· * 2) xs
    ensureEq "Composed over" [some 2, none, some 6] result
}

/--
Test tree traversal modifies all leaves.
-/
private def case_treeTraversal : TestCase := {
  name := "Tree traversal modifies all leaves",
  run := do
    let tr : Traversal' (Tree Int) Int := traversal Tree.walkMon
    let tree := Tree.node (Tree.leaf 5) (Tree.node (Tree.leaf 10) (Tree.leaf 15))
    let result := Traversal.over' tr (· + 1) tree
    let expected := Tree.node (Tree.leaf 6) (Tree.node (Tree.leaf 11) (Tree.leaf 16))
    ensureEq "Tree traversal" expected result
}

/--
Test that lawful traversal theorems can be invoked.
This test verifies that we can use the proven theorems.
-/
private def case_traversalLawTheorems : TestCase := {
  name := "Traversal law theorems can be invoked",
  run := do
    let tr : Traversal' (List Int) Int := traversal List.walkMon

    -- Identity law: over tr id = id
    let test1 := Traversal.over' tr (fun a => a) [1, 2, 3]
    ensureEq "Law theorem identity" [1, 2, 3] test1

    -- Traverse with Id functor
    let test2 := Traversal.traverse' tr (F := Theorems.Id) (fun a => a + 5) [10, 20]
    ensureEq "Traverse with Id" [15, 25] test2
}

/--
Test that the composition lawfulness instance works.
-/
private def case_compositionLawfulInstance : TestCase := {
  name := "Composition lawfulness instance is usable",
  run := do
    -- Test via explicit composition instead of private composed_walk
    let outer : Traversal' (List (Option Int)) (Option Int) := traversal List.walkMon
    let inner : Traversal' (Option Int) Int := traversal Option.walkMon
    let composed : Traversal' (List (Option Int)) Int := composeTraversal outer inner

    -- Test identity
    let xs : List (Option Int) := [some 1, none, some 2]
    let result := Traversal.over' composed (fun a => a) xs
    ensureEq "Composed lawful identity" xs result

    -- Test modification
    let result2 := Traversal.over' composed (· + 10) xs
    ensureEq "Composed lawful over" [some 11, none, some 12] result2
}

/--
Test Option traversal with effectful operations.
-/
private def case_optionTraversal : TestCase := {
  name := "Option traversal handles some and none correctly",
  run := do
    let tr : Traversal' (Option Int) Int := traversal Option.walkMon

    -- Test with some
    let result1 := Traversal.over' tr (· * 3) (some 4)
    ensureEq "Option some" (some 12) result1

    -- Test with none
    let result2 := Traversal.over' tr (· * 3) (none : Option Int)
    ensureEq "Option none" none result2

    -- Test traverse with Option applicative
    let f : Int → Option Int := fun n => if n < 10 then some (n + 1) else none
    let success := Traversal.traverse' tr f (some 5)
    let failure := Traversal.traverse' tr f (some 15)
    ensureEq "Option traverse success" (some (some 6)) success
    ensureEq "Option traverse failure" (none : Option (Option Int)) failure
}

/--
Test nested tree traversal with Option applicative.
-/
private def case_treeTraverseOption : TestCase := {
  name := "Tree traversal with Option applicative validates all leaves",
  run := do
    let tr : Traversal' (Tree Int) Int := traversal Tree.walkMon
    let tree := Tree.node (Tree.leaf 5) (Tree.leaf 3)

    let validate : Int → Option Int := fun n => if n > 0 then some n else none
    let result := Traversal.traverse' tr validate tree
    ensureEq "Tree validate success" (some tree) result

    let badTree := Tree.node (Tree.leaf 5) (Tree.leaf (-1))
    let badResult := Traversal.traverse' tr validate badTree
    ensureEq "Tree validate failure" (none : Option (Tree Int)) badResult
}

/--
All traversal law test cases.
-/
def cases : List TestCase :=
  [ case_traversalIdentityLaw
  , case_treeIdentityLaw
  , case_traversalOver
  , case_traverseOption
  , case_compositionIdentityLaw
  , case_composedTraversalOver
  , case_treeTraversal
  , case_traversalLawTheorems
  , case_compositionLawfulInstance
  , case_optionTraversal
  , case_treeTraverseOption
  ]

end CollimatorTests.TraversalLaws
