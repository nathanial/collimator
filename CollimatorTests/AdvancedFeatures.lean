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

testSuite "Advanced Features"

/-! ## String Optics Tests -/

test "String.chars: iso to List Char" := do
  let s := "hello"
  let charsIso : Iso' String (List Char) := chars
  let cs := s ^. charsIso
  ensureEq "chars forward" ['h', 'e', 'l', 'l', 'o'] cs
  let s' := review' charsIso ['w', 'o', 'r', 'l', 'd']
  ensureEq "chars backward" "world" s'

test "String.traversed: modify all characters" := do
  let s := "abc"
  let result := s & traversed %~ Char.toUpper
  ensureEq "toUpper all" "ABC" result

test "String.traversed: collect characters" := do
  let s := "xyz"
  let cs := s ^.. traversed
  ensureEq "collect chars" ['x', 'y', 'z'] cs

test "String.itraversed: indexed access" := do
  let s := "abc"
  let indexed := s ^.. Collimator.Instances.String.itraversed
  ensureEq "indexed chars" [(0, 'a'), (1, 'b'), (2, 'c')] indexed

test "String HasAt: valid index" := do
  let s := "hello"
  let c := s ^. atLens (ι := Nat) (s := String) (a := Char) 1
  ensureEq "char at 1" (some 'e') c

test "String HasAt: invalid index" := do
  let s := "hi"
  let c := s ^. atLens (ι := Nat) (s := String) (a := Char) 10
  ensureEq "char at 10" none c

test "String HasIx: modify at index" := do
  let s := "cat"
  let result := s & ix (ι := Nat) (s := String) (a := Char) 1 %~ (fun _ => 'o')
  ensureEq "modify char" "cot" result

test "String HasIx: out of bounds is no-op" := do
  let s := "dog"
  let result := s & ix (ι := Nat) (s := String) (a := Char) 100 %~ (fun _ => 'x')
  ensureEq "no-op" "dog" result

/-! ## Bifunctor Traversal Tests -/

test "both: traverse both components of pair" := do
  let pair := (3, 5)
  let result := pair & both %~ (· * 2)
  ensureEq "double both" (6, 10) result

test "both: collect both values" := do
  let pair := ("a", "b")
  let result := pair ^.. both
  ensureEq "collect both" ["a", "b"] result

test "both': monomorphic version" := do
  let pair := (10, 20)
  let result := pair & both' Int %~ (· + 1)
  ensureEq "both' increment" (11, 21) result

test "chosen: traverse left branch" := do
  let s : Sum Int Int := Sum.inl 42
  let result := s & chosen %~ (· * 2)
  ensureEq "double left" (Sum.inl 84) result

test "chosen: traverse right branch" := do
  let s : Sum Int Int := Sum.inr 99
  let result := s & chosen %~ (· + 1)
  ensureEq "increment right" (Sum.inr 100) result

test "chosen: collect from either branch" := do
  let left : Sum String String := Sum.inl "hello"
  let right : Sum String String := Sum.inr "world"
  let l := left ^.. chosen
  let r := right ^.. chosen
  ensureEq "left value" ["hello"] l
  ensureEq "right value" ["world"] r

test "chosen': monomorphic version" := do
  let s : Sum Int Int := Sum.inl 5
  let result := s & chosen' Int %~ (· * 10)
  ensureEq "chosen' scale" (Sum.inl 50) result

test "swapped: swap pair components" := do
  let pair := (1, 2)
  let swappedIso : Iso' (Int × Int) (Int × Int) := swapped
  let result := pair ^. swappedIso
  ensureEq "swapped" (2, 1) result

test "swappedSum: swap sum branches" := do
  let left : Sum Int Int := Sum.inl 42
  let right : Sum Int Int := Sum.inr 99
  let swappedSumIso : Iso' (Sum Int Int) (Sum Int Int) := swappedSum
  let l' := left ^. swappedSumIso
  let r' := right ^. swappedSumIso
  ensureEq "swap left" (Sum.inr 42) l'
  ensureEq "swap right" (Sum.inl 99) r'

test "beside: traverse both sides of pair" := do
  let pair := ([1, 2], [3, 4])
  let listTrav : Traversal' (List Int) Int := Collimator.Instances.List.traversed
  let t : Traversal' (List Int × List Int) Int := beside listTrav listTrav
  let result := pair & t %~ (· + 1)
  ensureEq "increment both lists" ([2, 3], [4, 5]) result

test "beside: collect from both sides" := do
  let pair := (["a", "b"], ["c"])
  let listTrav : Traversal' (List String) String := Collimator.Instances.List.traversed
  let t : Traversal' (List String × List String) String := beside listTrav listTrav
  let result := pair ^.. t
  ensureEq "collect all strings" ["a", "b", "c"] result

test "beside': monomorphic version" := do
  let pair := ([10, 20], [30])
  let listTrav : Traversal' (List Int) Int := Collimator.Instances.List.traversed
  let t : Traversal' (List Int × List Int) Int := beside' listTrav listTrav
  let result := pair & t %~ (· * 2)
  ensureEq "double all" ([20, 40], [60]) result

test "beside: heterogeneous source types" := do
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

test "Plated List: children of list" := do
  let xs := [1, 2, 3, 4]
  let cs := childrenOf xs
  -- List's plate focuses on the tail
  ensureEq "list children" [[2, 3, 4]] cs

test "Plated List: overChildren" := do
  let xs := [1, 2, 3]
  -- Reverse the tail
  let result := overChildren List.reverse xs
  ensureEq "reverse tail" [1, 3, 2] result

test "Plated Option: no children" := do
  let x : Option Int := some 42
  let cs := childrenOf x
  ensureEq "option has no children" ([] : List (Option Int)) cs

test "Plated SimpleTree: children of node" := do
  let leaf1 := SimpleTree.leaf 1
  let leaf2 := SimpleTree.leaf 2
  let tree := SimpleTree.node leaf1 leaf2
  let cs := childrenOf tree
  ensureEq "tree children count" 2 cs.length

test "Plated SimpleTree: children of leaf" := do
  let leaf := SimpleTree.leaf 42
  let cs := childrenOf leaf
  ensureEq "leaf has no children" ([] : List SimpleTree) cs

test "transform: bottom-up transformation" := do
  let leaf1 := SimpleTree.leaf 1
  let leaf2 := SimpleTree.leaf 2
  let tree := SimpleTree.node leaf1 leaf2
  -- Double all leaf values
  let doubleLeaves : SimpleTree → SimpleTree
    | SimpleTree.leaf n => SimpleTree.leaf (n * 2)
    | t => t
  let result := transform doubleLeaves tree
  ensureEq "transform sum" 6 (sumLeaves result)  -- (1*2) + (2*2) = 6

test "universeList: collect all nodes" := do
  let leaf1 := SimpleTree.leaf 1
  let leaf2 := SimpleTree.leaf 2
  let tree := SimpleTree.node leaf1 leaf2
  let all := universeList tree
  -- Should include root + 2 leaves = 3 nodes
  ensureEq "universe count" 3 all.length

test "cosmosCount: count all nodes" := do
  let leaf1 := SimpleTree.leaf 1
  let leaf2 := SimpleTree.leaf 2
  let inner := SimpleTree.node leaf1 leaf2
  let tree := SimpleTree.node inner (SimpleTree.leaf 3)
  -- Tree structure: node(node(leaf, leaf), leaf) = 5 nodes
  ensureEq "cosmos count" 5 (cosmosCount tree)

test "depth: measure tree depth" := do
  let leaf := SimpleTree.leaf 1
  ensureEq "leaf depth" 1 (depth leaf)
  let shallow := SimpleTree.node leaf leaf
  ensureEq "shallow depth" 2 (depth shallow)
  let deep := SimpleTree.node shallow leaf
  ensureEq "deep depth" 3 (depth deep)

test "allOf: check all nodes" := do
  let tree := SimpleTree.node (SimpleTree.leaf 2) (SimpleTree.leaf 4)
  let isEvenLeaf : SimpleTree → Bool
    | SimpleTree.leaf n => n % 2 == 0
    | _ => true
  ensure (allOf isEvenLeaf tree) "all leaves even"

test "anyOf: check any node" := do
  let tree := SimpleTree.node (SimpleTree.leaf 1) (SimpleTree.leaf 2)
  let isTwo : SimpleTree → Bool
    | SimpleTree.leaf 2 => true
    | _ => false
  ensure (anyOf isTwo tree) "found a two"

test "findOf: find matching node" := do
  let tree := SimpleTree.node (SimpleTree.leaf 1) (SimpleTree.leaf 42)
  let is42 : SimpleTree → Bool
    | SimpleTree.leaf 42 => true
    | _ => false
  let found := findOf is42 tree
  ensure found.isSome "found 42"

test "rewrite: iterative rewriting" := do
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

#generate_tests

end CollimatorTests.AdvancedFeatures
