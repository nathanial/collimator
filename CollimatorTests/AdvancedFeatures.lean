import CollimatorTests.Framework
import Collimator.Prelude
import Collimator.Instances

/-!
# Tests for Priority 5: Advanced Features

Tests for:
- String optics (chars, traversed, HasAt/HasIx)
- Bifunctor traversals (both, chosen)
- Plated typeclass (transform, rewrite, universe)
-/

open Collimator
open Collimator.Instances.String
open Collimator.Combinators.Bitraversal
open Collimator.Combinators.Plated
open Collimator.Indexed
open CollimatorTests
open scoped Collimator.Operators

namespace CollimatorTests.AdvancedFeatures

/-! ## String Optics Tests -/

def stringTests : List TestCase := [
  {
    name := "String.chars: iso to List Char"
    run := do
      let s := "hello"
      let charsIso : Iso' String (List Char) := chars
      let cs := s ^. charsIso
      ensureEq "chars forward" ['h', 'e', 'l', 'l', 'o'] cs
      let s' := review' charsIso ['w', 'o', 'r', 'l', 'd']
      ensureEq "chars backward" "world" s'
  },
  {
    name := "String.traversed: modify all characters"
    run := do
      let s := "abc"
      let result := s & traversed %~ Char.toUpper
      ensureEq "toUpper all" "ABC" result
  },
  {
    name := "String.traversed: collect characters"
    run := do
      let s := "xyz"
      let cs := s ^.. traversed
      ensureEq "collect chars" ['x', 'y', 'z'] cs
  },
  {
    name := "String.itraversed: indexed access"
    run := do
      let s := "abc"
      let indexed := s ^.. Collimator.Instances.String.itraversed
      ensureEq "indexed chars" [(0, 'a'), (1, 'b'), (2, 'c')] indexed
  },
  {
    name := "String HasAt: valid index"
    run := do
      let s := "hello"
      let c := s ^. atLens (ι := Nat) (s := String) (a := Char) 1
      ensureEq "char at 1" (some 'e') c
  },
  {
    name := "String HasAt: invalid index"
    run := do
      let s := "hi"
      let c := s ^. atLens (ι := Nat) (s := String) (a := Char) 10
      ensureEq "char at 10" none c
  },
  {
    name := "String HasIx: modify at index"
    run := do
      let s := "cat"
      let result := s & ix (ι := Nat) (s := String) (a := Char) 1 %~ (fun _ => 'o')
      ensureEq "modify char" "cot" result
  },
  {
    name := "String HasIx: out of bounds is no-op"
    run := do
      let s := "dog"
      let result := s & ix (ι := Nat) (s := String) (a := Char) 100 %~ (fun _ => 'x')
      ensureEq "no-op" "dog" result
  }
]

/-! ## Bifunctor Traversal Tests -/

def bitraversalTests : List TestCase := [
  {
    name := "both: traverse both components of pair"
    run := do
      let pair := (3, 5)
      let result := pair & both %~ (· * 2)
      ensureEq "double both" (6, 10) result
  },
  {
    name := "both: collect both values"
    run := do
      let pair := ("a", "b")
      let result := pair ^.. both
      ensureEq "collect both" ["a", "b"] result
  },
  {
    name := "both': monomorphic version"
    run := do
      let pair := (10, 20)
      let result := pair & both' Int %~ (· + 1)
      ensureEq "both' increment" (11, 21) result
  },
  {
    name := "chosen: traverse left branch"
    run := do
      let s : Sum Int Int := Sum.inl 42
      let result := s & chosen %~ (· * 2)
      ensureEq "double left" (Sum.inl 84) result
  },
  {
    name := "chosen: traverse right branch"
    run := do
      let s : Sum Int Int := Sum.inr 99
      let result := s & chosen %~ (· + 1)
      ensureEq "increment right" (Sum.inr 100) result
  },
  {
    name := "chosen: collect from either branch"
    run := do
      let left : Sum String String := Sum.inl "hello"
      let right : Sum String String := Sum.inr "world"
      let l := left ^.. chosen
      let r := right ^.. chosen
      ensureEq "left value" ["hello"] l
      ensureEq "right value" ["world"] r
  },
  {
    name := "chosen': monomorphic version"
    run := do
      let s : Sum Int Int := Sum.inl 5
      let result := s & chosen' Int %~ (· * 10)
      ensureEq "chosen' scale" (Sum.inl 50) result
  },
  {
    name := "swapped: swap pair components"
    run := do
      let pair := (1, 2)
      let swappedIso : Iso' (Int × Int) (Int × Int) := swapped
      let result := pair ^. swappedIso
      ensureEq "swapped" (2, 1) result
  },
  {
    name := "swappedSum: swap sum branches"
    run := do
      let left : Sum Int Int := Sum.inl 42
      let right : Sum Int Int := Sum.inr 99
      let swappedSumIso : Iso' (Sum Int Int) (Sum Int Int) := swappedSum
      let l' := left ^. swappedSumIso
      let r' := right ^. swappedSumIso
      ensureEq "swap left" (Sum.inr 42) l'
      ensureEq "swap right" (Sum.inl 99) r'
  },
  {
    name := "beside: traverse both sides of pair"
    run := do
      let pair := ([1, 2], [3, 4])
      let listTrav : Traversal' (List Int) Int := Collimator.Instances.List.traversed
      let t : Traversal' (List Int × List Int) Int := beside listTrav listTrav
      let result := pair & t %~ (· + 1)
      ensureEq "increment both lists" ([2, 3], [4, 5]) result
  },
  {
    name := "beside: collect from both sides"
    run := do
      let pair := (["a", "b"], ["c"])
      let listTrav : Traversal' (List String) String := Collimator.Instances.List.traversed
      let t : Traversal' (List String × List String) String := beside listTrav listTrav
      let result := pair ^.. t
      ensureEq "collect all strings" ["a", "b", "c"] result
  },
  {
    name := "beside': monomorphic version"
    run := do
      let pair := ([10, 20], [30])
      let listTrav : Traversal' (List Int) Int := Collimator.Instances.List.traversed
      let t : Traversal' (List Int × List Int) Int := beside' listTrav listTrav
      let result := pair & t %~ (· * 2)
      ensureEq "double all" ([20, 40], [60]) result
  },
  {
    name := "beside: heterogeneous source types"
    run := do
      -- Left is Option, right is List
      let pair : (Option Int × List Int) := (some 5, [1, 2])
      let optTrav : Traversal' (Option Int) Int := Collimator.traversal
        (fun {F} [Applicative F] (f : Int → F Int) (opt : Option Int) =>
          match opt with
          | none => pure none
          | some x => Functor.map some (f x))
      let listTrav : Traversal' (List Int) Int := Collimator.Instances.List.traversed
      let t : Traversal' (Option Int × List Int) Int := beside optTrav listTrav
      let result := pair & t %~ (· + 10)
      ensureEq "traverse option and list" (some 15, [11, 12]) result
  }
]

/-! ## Plated Tests -/

-- Simple tree for testing Plated
private inductive SimpleTree where
  | leaf : Int → SimpleTree
  | node : SimpleTree → SimpleTree → SimpleTree
deriving BEq, Repr

private instance : Plated SimpleTree where
  plate := Collimator.traversal
    (fun {F : Type → Type} [Applicative F]
      (f : SimpleTree → F SimpleTree) (t : SimpleTree) =>
        match t with
        | SimpleTree.leaf _ => pure t
        | SimpleTree.node l r => pure SimpleTree.node <*> f l <*> f r)

private def sumLeaves : SimpleTree → Int
  | SimpleTree.leaf n => n
  | SimpleTree.node l r => sumLeaves l + sumLeaves r

def platedTests : List TestCase := [
  {
    name := "Plated List: children of list"
    run := do
      let xs := [1, 2, 3, 4]
      let cs := childrenOf xs
      -- List's plate focuses on the tail
      ensureEq "list children" [[2, 3, 4]] cs
  },
  {
    name := "Plated List: overChildren"
    run := do
      let xs := [1, 2, 3]
      -- Reverse the tail
      let result := overChildren List.reverse xs
      ensureEq "reverse tail" [1, 3, 2] result
  },
  {
    name := "Plated Option: no children"
    run := do
      let x : Option Int := some 42
      let cs := childrenOf x
      ensureEq "option has no children" ([] : List (Option Int)) cs
  },
  {
    name := "Plated SimpleTree: children of node"
    run := do
      let leaf1 := SimpleTree.leaf 1
      let leaf2 := SimpleTree.leaf 2
      let tree := SimpleTree.node leaf1 leaf2
      let cs := childrenOf tree
      ensureEq "tree children count" 2 cs.length
  },
  {
    name := "Plated SimpleTree: children of leaf"
    run := do
      let leaf := SimpleTree.leaf 42
      let cs := childrenOf leaf
      ensureEq "leaf has no children" ([] : List SimpleTree) cs
  },
  {
    name := "transform: bottom-up transformation"
    run := do
      let leaf1 := SimpleTree.leaf 1
      let leaf2 := SimpleTree.leaf 2
      let tree := SimpleTree.node leaf1 leaf2
      -- Double all leaf values
      let doubleLeaves : SimpleTree → SimpleTree
        | SimpleTree.leaf n => SimpleTree.leaf (n * 2)
        | t => t
      let result := transform doubleLeaves tree
      ensureEq "transform sum" 6 (sumLeaves result)  -- (1*2) + (2*2) = 6
  },
  {
    name := "universeList: collect all nodes"
    run := do
      let leaf1 := SimpleTree.leaf 1
      let leaf2 := SimpleTree.leaf 2
      let tree := SimpleTree.node leaf1 leaf2
      let all := universeList tree
      -- Should include root + 2 leaves = 3 nodes
      ensureEq "universe count" 3 all.length
  },
  {
    name := "cosmosCount: count all nodes"
    run := do
      let leaf1 := SimpleTree.leaf 1
      let leaf2 := SimpleTree.leaf 2
      let inner := SimpleTree.node leaf1 leaf2
      let tree := SimpleTree.node inner (SimpleTree.leaf 3)
      -- Tree structure: node(node(leaf, leaf), leaf) = 5 nodes
      ensureEq "cosmos count" 5 (cosmosCount tree)
  },
  {
    name := "depth: measure tree depth"
    run := do
      let leaf := SimpleTree.leaf 1
      ensureEq "leaf depth" 1 (depth leaf)
      let shallow := SimpleTree.node leaf leaf
      ensureEq "shallow depth" 2 (depth shallow)
      let deep := SimpleTree.node shallow leaf
      ensureEq "deep depth" 3 (depth deep)
  },
  {
    name := "allOf: check all nodes"
    run := do
      let tree := SimpleTree.node (SimpleTree.leaf 2) (SimpleTree.leaf 4)
      let isEvenLeaf : SimpleTree → Bool
        | SimpleTree.leaf n => n % 2 == 0
        | _ => true
      ensure (allOf isEvenLeaf tree) "all leaves even"
  },
  {
    name := "anyOf: check any node"
    run := do
      let tree := SimpleTree.node (SimpleTree.leaf 1) (SimpleTree.leaf 2)
      let isTwo : SimpleTree → Bool
        | SimpleTree.leaf 2 => true
        | _ => false
      ensure (anyOf isTwo tree) "found a two"
  },
  {
    name := "findOf: find matching node"
    run := do
      let tree := SimpleTree.node (SimpleTree.leaf 1) (SimpleTree.leaf 42)
      let is42 : SimpleTree → Bool
        | SimpleTree.leaf 42 => true
        | _ => false
      let found := findOf is42 tree
      ensure found.isSome "found 42"
  },
  {
    name := "rewrite: iterative rewriting"
    run := do
      -- Rewrite nested nodes to simplify
      let leaf := SimpleTree.leaf 1
      let tree := SimpleTree.node leaf leaf
      -- Rewrite: if both children are the same leaf, collapse to that leaf
      let simplify : SimpleTree → Option SimpleTree
        | SimpleTree.node (SimpleTree.leaf n) (SimpleTree.leaf m) =>
            if n == m then some (SimpleTree.leaf n) else none
        | _ => none
      let result := rewrite simplify tree
      -- node(leaf 1, leaf 1) should become leaf 1
      ensureEq "rewrite result" (SimpleTree.leaf 1) result
  }
]

/-! ## All Tests -/

def cases : List TestCase :=
  stringTests ++ bitraversalTests ++ platedTests

end CollimatorTests.AdvancedFeatures
