import Collimator.Prelude

/-!
# Tree Traversal with Optics

This example demonstrates using traversals with recursive tree structures,
showing how optics can focus on all nodes at a particular level or
matching a condition.
-/

open Collimator
open scoped Collimator.Operators

/-! ## Tree Types -/

/-- A simple binary tree -/
inductive BinTree (α : Type) where
  | leaf : BinTree α
  | node : α → BinTree α → BinTree α → BinTree α
  deriving Repr, Inhabited

/-- A rose tree (n-ary tree) -/
structure RoseTree (α : Type) where
  value : α
  children : List (RoseTree α)
  deriving Repr, Inhabited

/-- A file system tree -/
inductive FSEntry where
  | file : String → Nat → FSEntry  -- name, size
  | dir : String → List FSEntry → FSEntry  -- name, contents
  deriving Repr, Inhabited

namespace BinTree

/-! ## Binary Tree Optics -/

/-- Prism focusing on node value (fails on leaf) -/
def _nodeValue {α : Type} : Prism' (BinTree α) α :=
  prismFromPartial
    (fun | node v _ _ => some v | leaf => none)
    (fun v => node v leaf leaf)

/-- Lens for the value of a node (partial - assumes node) -/
def nodeValue {α : Type} [Inhabited α] : Lens' (BinTree α) α :=
  lens'
    (fun | node v _ _ => v | leaf => default)
    (fun t v => match t with
      | node _ l r => node v l r
      | leaf => leaf)

/-- Lens for left subtree of a node -/
def leftTree {α : Type} : Lens' (BinTree α) (BinTree α) :=
  lens'
    (fun | node _ l _ => l | leaf => leaf)
    (fun t l => match t with
      | node v _ r => node v l r
      | leaf => leaf)

/-- Lens for right subtree of a node -/
def rightTree {α : Type} : Lens' (BinTree α) (BinTree α) :=
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
partial def mapTree {α β : Type} (f : α → β) : BinTree α → BinTree β
  | leaf => leaf
  | node v l r => node (f v) (mapTree f l) (mapTree f r)

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

/-- Traversal over immediate children using standard function composition -/
def immediateChildren {α : Type} : Traversal' (RoseTree α) (RoseTree α) :=
  childrenLens ∘ Collimator.Instances.List.traversed

/-- Collect all values from a rose tree (depth-first) -/
partial def collectValues {α : Type} (t : RoseTree α) : List α :=
  t.value :: t.children.flatMap collectValues

/-- Map over all values in a rose tree (monomorphic - same type) -/
partial def mapValues {α : Type} [Inhabited α] (f : α → α) (t : RoseTree α) : RoseTree α :=
  { value := f t.value, children := t.children.map (mapValues f) }

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

/-- Collect all entries recursively -/
partial def collectAll : FSEntry → List FSEntry
  | e@(file _ _) => [e]
  | e@(dir _ contents) => e :: contents.flatMap collectAll

/-- Collect all file sizes -/
partial def collectFileSizes : FSEntry → List Nat
  | file _ s => [s]
  | dir _ contents => contents.flatMap collectFileSizes

/-- Collect all names -/
partial def collectNames : FSEntry → List String
  | file n _ => [n]
  | dir n contents => n :: contents.flatMap collectNames

/-- Calculate total size -/
partial def totalSize : FSEntry → Nat
  | file _ s => s
  | dir _ contents => contents.foldl (fun acc e => acc + totalSize e) 0

/-- Double all file sizes -/
partial def doubleSizes : FSEntry → FSEntry
  | file n s => file n (s * 2)
  | dir n contents => dir n (contents.map doubleSizes)

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

  let doubled := sampleBinTree & BinTree.values %~ (· * 2)
  IO.println s!"  After doubling: {BinTree.toList doubled}"

  -- Collect all values using toListTraversal
  let values := sampleBinTree ^.. BinTree.values
  IO.println s!"  Collected via traversal: {values}"
  IO.println ""

  -- Rose tree
  IO.println "Rose Tree:"
  IO.println s!"  Root value: {sampleRoseTree ^. RoseTree.rootValue}"
  IO.println s!"  Size: {RoseTree.size sampleRoseTree}"
  IO.println s!"  Depth: {RoseTree.depth sampleRoseTree}"

  let allVals := RoseTree.collectValues sampleRoseTree
  IO.println s!"  All values: {allVals}"

  let uppercased := RoseTree.mapValues String.toUpper sampleRoseTree
  let upperedVals := RoseTree.collectValues uppercased
  IO.println s!"  After uppercase: {upperedVals}"
  IO.println ""

  -- File system
  IO.println "File System:"
  IO.println s!"  Total size: {FSEntry.totalSize sampleFS} bytes"

  -- Get all file sizes
  let sizes := FSEntry.collectFileSizes sampleFS
  IO.println s!"  All file sizes: {sizes}"

  -- Get all entry names
  let names := FSEntry.collectNames sampleFS
  IO.println s!"  All entry names: {names}"

  -- Double all file sizes (for testing)
  let expanded := FSEntry.doubleSizes sampleFS
  IO.println s!"  Total size after doubling: {FSEntry.totalSize expanded} bytes"

  IO.println ""
  IO.println "=== Optics Usage ==="

  -- Using traversal with BinTree
  let sum := Fold.sumOfTraversal BinTree.values sampleBinTree
  IO.println s!"  Sum of binary tree values: {sum}"

  let count := Fold.lengthOfTraversal BinTree.values sampleBinTree
  IO.println s!"  Count of binary tree nodes: {count}"

  -- Using immediate children traversal
  let childCount := Fold.lengthOfTraversal RoseTree.immediateChildren sampleRoseTree
  IO.println s!"  Rose tree immediate children: {childCount}"

#eval examples
