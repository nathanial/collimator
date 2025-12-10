/-!
# Tree Traversal with Optics

This example demonstrates using traversals with recursive tree structures,
showing how optics can focus on all nodes at a particular level or
matching a condition.
-/

import Collimator.Prelude

open Collimator
open Collimator.Poly
open Collimator.Combinators
open scoped Collimator.Operators

/-! ## Tree Types -/

/-- A simple binary tree -/
inductive BinTree (α : Type) where
  | leaf : BinTree α
  | node : α → BinTree α → BinTree α → BinTree α
  deriving Repr

/-- A rose tree (n-ary tree) -/
structure RoseTree (α : Type) where
  value : α
  children : List (RoseTree α)
  deriving Repr

/-- A file system tree -/
inductive FSEntry where
  | file : String → Nat → FSEntry  -- name, size
  | dir : String → List FSEntry → FSEntry  -- name, contents
  deriving Repr

namespace BinTree

/-! ## Binary Tree Optics -/

/-- Prism focusing on node value (fails on leaf) -/
def _nodeValue {α : Type} : Prism' (BinTree α) α :=
  prismFromPartial
    (fun | node v _ _ => some v | leaf => none)
    (fun v => node v leaf leaf)

/-- Lens for the value of a node (partial - assumes node) -/
def nodeValue {α : Type} : Lens' (BinTree α) α :=
  lens'
    (fun | node v _ _ => v | leaf => default)
    (fun t v => match t with
      | node _ l r => node v l r
      | leaf => leaf)

/-- Lens for left subtree of a node -/
def leftTree {α : Type} [Inhabited α] : Lens' (BinTree α) (BinTree α) :=
  lens'
    (fun | node _ l _ => l | leaf => leaf)
    (fun t l => match t with
      | node v _ r => node v l r
      | leaf => leaf)

/-- Lens for right subtree of a node -/
def rightTree {α : Type} [Inhabited α] : Lens' (BinTree α) (BinTree α) :=
  lens'
    (fun | node _ _ r => r | leaf => leaf)
    (fun t r => match t with
      | node v l _ => node v l r
      | leaf => leaf)

/-- Collect all values in a binary tree (in-order) -/
partial def toList {α : Type} : BinTree α → List α
  | leaf => []
  | node v l r => toList l ++ [v] ++ toList r

/-- Map over all values in a binary tree -/
partial def map {α β : Type} (f : α → β) : BinTree α → BinTree β
  | leaf => leaf
  | node v l r => node (f v) (map f l) (map f r)

/-- A traversal focusing on all values in the tree -/
def values {α : Type} : Traversal' (BinTree α) α :=
  Collimator.traversal fun {F} [Applicative F] f t =>
    let rec go : BinTree α → F (BinTree α)
      | leaf => pure leaf
      | node v l r => node <$> f v <*> go l <*> go r
    go t

end BinTree

namespace RoseTree

/-! ## Rose Tree Optics -/

/-- Lens focusing on the root value -/
def rootValue {α : Type} : Lens' (RoseTree α) α :=
  lens' (·.value) (fun t v => { t with value := v })

/-- Lens focusing on the children list -/
def childrenLens {α : Type} : Lens' (RoseTree α) (List (RoseTree α)) :=
  lens' (·.children) (fun t cs => { t with children := cs })

/-- Traversal over immediate children -/
def immediateChildren {α : Type} : Traversal' (RoseTree α) (RoseTree α) :=
  childrenLens ⊚ Collimator.Instances.List.traversed

/-- Traversal over all values in the tree (breadth-first would need more work) -/
def allValues {α : Type} : Traversal' (RoseTree α) α :=
  Collimator.traversal fun {F} [Applicative F] f t =>
    let rec go (tree : RoseTree α) : F (RoseTree α) :=
      let goChildren : List (RoseTree α) → F (List (RoseTree α))
        | [] => pure []
        | c :: cs => (· :: ·) <$> go c <*> goChildren cs
      RoseTree.mk <$> f tree.value <*> goChildren tree.children
    go t

/-- Count total nodes -/
partial def size {α : Type} (t : RoseTree α) : Nat :=
  1 + t.children.foldl (fun acc c => acc + size c) 0

/-- Get depth of tree -/
partial def depth {α : Type} (t : RoseTree α) : Nat :=
  1 + (t.children.map depth |>.foldl max 0)

end RoseTree

namespace FSEntry

/-! ## File System Optics -/

/-- Prism for file entries -/
def _file : Prism' FSEntry (String × Nat) :=
  prismFromPartial
    (fun | file n s => some (n, s) | _ => none)
    (fun (n, s) => file n s)

/-- Prism for directory entries -/
def _dir : Prism' FSEntry (String × List FSEntry) :=
  prismFromPartial
    (fun | dir n cs => some (n, cs) | _ => none)
    (fun (n, cs) => dir n cs)

/-- Get entry name -/
def getName : FSEntry → String
  | file n _ => n
  | dir n _ => n

/-- Lens for entry name -/
def nameLens : Lens' FSEntry String :=
  lens'
    getName
    (fun e n => match e with
      | file _ s => file n s
      | dir _ cs => dir n cs)

/-- Prism for file size (only for files) -/
def fileSize : Prism' FSEntry Nat :=
  prismFromPartial
    (fun | file _ s => some s | _ => none)
    (fun s => file "unnamed" s)

/-- Traversal over directory contents -/
def dirContents : Traversal' FSEntry FSEntry :=
  Collimator.traversal fun {F} [Applicative F] f e =>
    match e with
    | file n s => pure (file n s)
    | dir n contents =>
      let rec goList : List FSEntry → F (List FSEntry)
        | [] => pure []
        | x :: xs => (· :: ·) <$> f x <*> goList xs
      dir n <$> goList contents

/-- Recursively traverse all entries -/
def allEntries : Traversal' FSEntry FSEntry :=
  Collimator.traversal fun {F} [Applicative F] f e =>
    let rec go (entry : FSEntry) : F FSEntry :=
      match entry with
      | file n s => f (file n s)
      | dir n contents =>
        let goList : List FSEntry → F (List FSEntry)
          | [] => pure []
          | x :: xs => (· :: ·) <$> go x <*> goList xs
        f entry *> (dir n <$> goList contents)
    go e

/-- Calculate total size -/
partial def totalSize : FSEntry → Nat
  | file _ s => s
  | dir _ contents => contents.foldl (fun acc e => acc + totalSize e) 0

end FSEntry

/-! ## Example Data -/

def sampleBinTree : BinTree Int :=
  .node 5
    (.node 3
      (.node 1 .leaf .leaf)
      (.node 4 .leaf .leaf))
    (.node 8
      (.node 7 .leaf .leaf)
      (.node 9 .leaf .leaf))

def sampleRoseTree : RoseTree String :=
  { value := "root"
  , children := [
      { value := "child1"
      , children := [
          { value := "grandchild1", children := [] },
          { value := "grandchild2", children := [] }
        ]
      },
      { value := "child2"
      , children := [
          { value := "grandchild3", children := [] }
        ]
      },
      { value := "child3", children := [] }
    ]
  }

def sampleFS : FSEntry :=
  .dir "project" [
    .file "README.md" 1024,
    .file "Makefile" 512,
    .dir "src" [
      .file "main.c" 4096,
      .file "utils.c" 2048,
      .dir "include" [
        .file "utils.h" 256
      ]
    ],
    .dir "tests" [
      .file "test_main.c" 1024
    ]
  ]

/-! ## Example Usage -/

def examples : IO Unit := do
  IO.println "=== Tree Traversal Examples ==="
  IO.println ""

  -- Binary tree
  IO.println "Binary Tree:"
  IO.println s!"  Original values: {BinTree.toList sampleBinTree}"

  let doubled := over BinTree.values (· * 2) sampleBinTree
  IO.println s!"  After doubling: {BinTree.toList doubled}"

  -- Collect all values
  let values := Fold.toList BinTree.values sampleBinTree
  IO.println s!"  Collected via traversal: {values}"
  IO.println ""

  -- Rose tree
  IO.println "Rose Tree:"
  IO.println s!"  Root value: {sampleRoseTree ^. RoseTree.rootValue}"
  IO.println s!"  Size: {RoseTree.size sampleRoseTree}"
  IO.println s!"  Depth: {RoseTree.depth sampleRoseTree}"

  let allVals := Fold.toList RoseTree.allValues sampleRoseTree
  IO.println s!"  All values: {allVals}"

  let uppercased := over RoseTree.allValues String.toUpper sampleRoseTree
  let upperedVals := Fold.toList RoseTree.allValues uppercased
  IO.println s!"  After uppercase: {upperedVals}"
  IO.println ""

  -- File system
  IO.println "File System:"
  IO.println s!"  Total size: {FSEntry.totalSize sampleFS} bytes"

  -- Get all file sizes
  let sizes := Fold.toList (FSEntry.allEntries ⊚ FSEntry.fileSize) sampleFS
  IO.println s!"  All file sizes: {sizes}"

  -- Get all entry names
  let names := Fold.toList (FSEntry.allEntries ⊚ FSEntry.nameLens) sampleFS
  IO.println s!"  All entry names: {names}"

  -- Double all file sizes (for testing)
  let expanded := over (FSEntry.allEntries ⊚ FSEntry.fileSize) (· * 2) sampleFS
  IO.println s!"  Total size after doubling: {FSEntry.totalSize expanded} bytes"

-- #eval examples
