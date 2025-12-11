import Collimator.Optics
import Collimator.Combinators
import Collimator.Operators
import Collimator.Instances
import CollimatorTests.Framework

namespace CollimatorTests.AdvancedShowcase.MindBending

open Collimator
open Collimator.Combinators
open Collimator.Combinators.Plated
open Collimator.Instances.Option (somePrism')
open scoped Collimator.Operators
open CollimatorTests

/-!
# Mind-Bending Examples

Showcase the most impressive and non-obvious capabilities:
- Self-referential optics (traversals that modify their own structure)
- Optics over functions (lenses into closures)
- Recursive traversals over tree-like structures
- Optics with phantom type parameters
- Van Laarhoven encoding tricks and equivalences
- "Impossible" seeming transformations made trivial
- Examples that would be very difficult without profunctor optics
-/

/-! ## Recursive Tree Structures -/

/-- Binary tree with values at leaves -/
inductive Tree (α : Type _) where
  | leaf : α → Tree α
  | node : Tree α → Tree α → Tree α
  deriving BEq, Repr

/-- Rose tree (n-ary tree) with values at nodes -/
inductive Rose (α : Type _) where
  | node : α → List (Rose α) → Rose α
  deriving BEq, Repr

instance [Inhabited α] : Inhabited (Rose α) where
  default := Rose.node default []

/-! ## Plated Instances -/

/-- Plated instance for binary trees - immediate children are the subtrees -/
instance : Plated (Tree α) where
  plate := traversal fun {F} [Applicative F] (f : Tree α → F (Tree α)) (t : Tree α) =>
    match t with
    | Tree.leaf a => pure (Tree.leaf a)
    | Tree.node l r => pure Tree.node <*> f l <*> f r

/-- Plated instance for rose trees - immediate children are in the children list -/
instance : Plated (Rose α) where
  plate := traversal fun {F} [Applicative F] (f : Rose α → F (Rose α)) (t : Rose α) =>
    match t with
    | Rose.node value children =>
        let rec walkList : List (Rose α) → F (List (Rose α))
          | [] => pure []
          | x :: xs => pure List.cons <*> f x <*> walkList xs
        pure (Rose.node value) <*> walkList children

/-! ## Leaf Traversals -/

/-- Applicative traversal over binary tree leaves -/
private def Tree.walkLeaves {F : Type _ → Type _} [Applicative F]
    (f : α → F α) : Tree α → F (Tree α)
  | Tree.leaf a => pure Tree.leaf <*> f a
  | Tree.node l r => pure Tree.node <*> Tree.walkLeaves f l <*> Tree.walkLeaves f r

/-- Traversal over binary tree leaves (values, not subtrees) -/
private def Tree.leaves : Traversal' (Tree α) α :=
  traversal Tree.walkLeaves

-- Rose.walk: Applicative traversal over rose tree node values
-- Note: Due to a Lean 4 compiler limitation with mutual recursive function specialization,
-- traversals defined this way cannot be used with StateT in some contexts.
mutual
  private def Rose.walk {α : Type _} {F : Type _ → Type _} [Applicative F]
      (f : α → F α) : Rose α → F (Rose α)
    | Rose.node value children =>
        pure Rose.node <*> f value <*> Rose.walkList f children

  private def Rose.walkList {α : Type _} {F : Type _ → Type _} [Applicative F]
      (f : α → F α) : List (Rose α) → F (List (Rose α))
    | [] => pure []
    | x :: xs => pure List.cons <*> Rose.walk f x <*> Rose.walkList f xs
end

/-- Traversal over rose tree node values -/
private def Rose.values : Traversal' (Rose α) α :=
  traversal Rose.walk

/-! ## Depth-Aware Traversals -/

/-- Depth-aware traversal over binary tree leaves -/
private def Tree.walkWithDepth {F : Type _ → Type _} [Applicative F]
    (f : Nat → α → F α) (depth : Nat) : Tree α → F (Tree α)
  | Tree.leaf a => pure Tree.leaf <*> f depth a
  | Tree.node l r =>
      pure Tree.node <*> Tree.walkWithDepth f (depth + 1) l <*> Tree.walkWithDepth f (depth + 1) r

/-- Depth-aware traversal for rose tree nodes -/
private def Rose.walkWithDepth {F : Type _ → Type _} [Applicative F]
    (f : Nat → α → F α) (depth : Nat) : Rose α → F (Rose α)
  | Rose.node value children =>
      let rec walkList (d : Nat) : List (Rose α) → F (List (Rose α))
        | [] => pure []
        | x :: xs => pure List.cons <*> Rose.walkWithDepth f d x <*> walkList d xs
      pure Rose.node <*> f depth value <*> walkList (depth + 1) children

/-! ## Test Cases -/

/-- Test: Basic recursive traversal over binary tree -/
private def case_binaryTreeTraversal : TestCase := {
  name := "Binary tree: recursive traversal modifies all leaves",
  run := do
    -- Build a binary tree:       node
    --                            /    \
    --                         leaf(5) node
    --                                /    \
    --                            leaf(10) leaf(15)
    let tree := Tree.node
      (Tree.leaf 5)
      (Tree.node (Tree.leaf 10) (Tree.leaf 15))

    -- Transform all leaves using Tree.leaves traversal
    let doubled := tree & Tree.leaves %~ (· * 2)
    let expected := Tree.node
      (Tree.leaf 10)
      (Tree.node (Tree.leaf 20) (Tree.leaf 30))

    ensureEq "All leaves doubled" expected doubled

    -- Collect all leaf values using Fold.toListTraversal
    let leaves := Fold.toListTraversal Tree.leaves tree
    ensureEq "All leaves collected" [5, 10, 15] leaves
}

/-- Test: Depth-aware recursive traversal using depth tracking -/
private def case_depthAwareTraversal : TestCase := {
  name := "Binary tree: depth-aware transformation using actual depth",
  run := do
    -- Create a tree with varying depths:
    --       node (depth 0)
    --       /           \
    --    leaf(1)      node (depth 1)
    --   depth 1       /         \
    --             leaf(2)     leaf(3)
    --            depth 2      depth 2
    let tree := Tree.node
      (Tree.leaf 1)
      (Tree.node (Tree.leaf 2) (Tree.leaf 3))

    -- Transform: add 100 * depth to each leaf value
    -- Leaf 1 is at depth 1: 1 + 100*1 = 101
    -- Leaf 2 is at depth 2: 2 + 100*2 = 202
    -- Leaf 3 is at depth 2: 3 + 100*2 = 203
    let addDepth (depth : Nat) (x : Int) : Id Int :=
      x + (100 * (depth : Int))

    let result := Tree.walkWithDepth addDepth 0 tree
    let expected := Tree.node
      (Tree.leaf 101)
      (Tree.node (Tree.leaf 202) (Tree.leaf 203))

    ensureEq "Values transformed by depth" expected result

    -- Verify we can also collect depth information
    let collectWithDepth (depth : Nat) (x : Int) : StateT (List (Nat × Int)) Id Int := do
      modify ((depth, x) :: ·)
      pure x

    let (_, depthInfo) := (Tree.walkWithDepth collectWithDepth 0 tree).run []
    ensureEq "Collected depth info" [(1, 1), (2, 2), (2, 3)] depthInfo.reverse
}

/-- Test: Rose tree (n-ary tree) recursive traversal -/
private def case_roseTreeTraversal : TestCase := {
  name := "Rose tree: n-ary recursive traversal with multiple children",
  run := do
    -- Build a rose tree:
    --          "root"
    --         /   |   \
    --      "a"   "b"  "c"
    --      /\         |
    --   "d" "e"      "f"

    let tree := Rose.node "root" [
      Rose.node "a" [
        Rose.node "d" [],
        Rose.node "e" []
      ],
      Rose.node "b" [],
      Rose.node "c" [
        Rose.node "f" []
      ]
    ]

    -- Transform all nodes to uppercase using Rose.values traversal
    let upper := tree & Rose.values %~ String.toUpper

    -- Verify root
    match upper with
    | Rose.node value children =>
      ensureEq "Root uppercase" "ROOT" value
      ensureEq "Three children" 3 children.length

      -- Verify first child
      match children.head? with
      | some (Rose.node value children) =>
        ensureEq "First child uppercase" "A" value
        ensureEq "First child has 2 children" 2 children.length
      | none => ensure false "Expected first child"

    -- Count all nodes using Plated.cosmosCount (works on tree structure, not values)
    -- This counts Rose nodes, not String values
    let nodeCount := cosmosCount tree
    ensureEq "Total node count (via Plated)" 7 nodeCount

    -- Also verify via collecting values
    let values := Fold.toListTraversal Rose.values tree
    ensureEq "Total value count" 7 values.length
}

/-- Test: Rose tree with deeply nested structure -/
private def case_deeplyNestedRoseTree : TestCase := {
  name := "Rose tree: deeply nested multi-way structure",
  run := do
    -- Build a deeply nested rose tree
    let deepTree := Rose.node 1 [
      Rose.node 2 [
        Rose.node 3 [],
        Rose.node 4 [
          Rose.node 5 []
        ]
      ],
      Rose.node 6 [
        Rose.node 7 [
          Rose.node 8 [],
          Rose.node 9 []
        ]
      ]
    ]

    -- Transform all values using Rose.values
    let multiplied := deepTree & Rose.values %~ (· * 10)

    -- Collect all values using Fold.toListTraversal
    let values := Fold.toListTraversal Rose.values multiplied
    ensureEq "All values multiplied by 10" [10, 20, 30, 40, 50, 60, 70, 80, 90] values

    -- Verify depth using Plated.depth
    let treeDepth := depth deepTree
    ensureEq "Tree depth (via Plated)" 4 treeDepth
}

/-- Test: Recursive validation with Option applicative -/
private def case_recursiveValidation : TestCase := {
  name := "Binary tree: recursive validation short-circuits on invalid node",
  run := do
    let tree1 := Tree.node
      (Tree.leaf 5)
      (Tree.node (Tree.leaf 10) (Tree.leaf 15))

    -- Validation: all values must be positive
    let validatePositive (x : Int) : Option Int :=
      if x > 0 then some x else none

    let result1 := Traversal.traverse' Tree.leaves validatePositive tree1
    match result1 with
    | some t => ensureEq "Valid tree passes" tree1 t
    | none => ensure false "Expected validation to succeed"

    -- Tree with negative value - should fail
    let tree2 := Tree.node
      (Tree.leaf 5)
      (Tree.node (Tree.leaf (-10)) (Tree.leaf 15))

    let result2 := Traversal.traverse' Tree.leaves validatePositive tree2
    match result2 with
    | none => pure ()  -- Expected: validation fails
    | some _ => ensure false "Expected validation to fail"

    -- Also demonstrate Plated.allOf for validation
    let allPositive := allOf (fun (t : Tree Int) =>
      match t with
      | Tree.leaf x => x > 0
      | Tree.node _ _ => true) tree1
    ensure allPositive "allOf reports all leaves positive"

    let allPositive2 := allOf (fun (t : Tree Int) =>
      match t with
      | Tree.leaf x => x > 0
      | Tree.node _ _ => true) tree2
    ensure (!allPositive2) "allOf detects negative leaf"
}

/-- Test: Recursive transformation with accumulating state -/
private def case_recursiveStatefulTransform : TestCase := {
  name := "Rose tree: compute running sum while transforming",
  run := do
    let tree := Rose.node 10 [
      Rose.node 20 [],
      Rose.node 30 [
        Rose.node 40 [],
        Rose.node 50 []
      ]
    ]

    -- Use direct Rose.walk for StateT traversal (works around compiler limitation)
    let tr : Traversal' (Rose Int) Int := traversal Rose.walk

    -- Replace each value with the running sum and add current value to sum
    let replaceWithSum (x : Int) : StateT Int Id Int := do
      let sum ← get
      set (sum + x)
      pure sum

    let (transformed, finalSum) := (Traversal.traverse' tr replaceWithSum tree).run 0

    -- Values should be: [0, 10, 30, 60, 100]
    -- Transform: 10->0 (sum before), 20->10, 30->30, 40->60, 50->100
    ensureEq "Final sum" 150 finalSum

    -- Verify root was replaced with 0 (initial sum)
    match transformed with
    | Rose.node value _ =>
      ensureEq "Root replaced with initial sum" 0 value

    -- Collect all transformed values using Fold.toListTraversal
    let transformedValues := Fold.toListTraversal tr transformed
    ensureEq "All transformed values are running sums" [0, 10, 30, 60, 100] transformedValues
}

/-- Test: Composing recursive traversals -/
private def case_composedRecursiveTraversal : TestCase := {
  name := "Composed traversal: Tree of Options",
  run := do
    -- Create a tree where each leaf contains an Option
    let treeOfOptions : Tree (Option Int) := Tree.node
      (Tree.leaf (some 5))
      (Tree.node (Tree.leaf none) (Tree.leaf (some 15)))

    -- Use Tree.leaves for the tree traversal, compose with somePrism'
    -- Tree.leaves : Traversal' (Tree (Option Int)) (Option Int)
    -- somePrism' Int : Prism' (Option Int) Int
    let composed : Traversal' (Tree (Option Int)) Int :=
      Tree.leaves ∘ somePrism' Int

    -- Transform: double all present values, skip None
    let doubled := treeOfOptions & composed %~ (· * 2)
    let expected := Tree.node
      (Tree.leaf (some 10))
      (Tree.node (Tree.leaf none) (Tree.leaf (some 30)))

    ensureEq "Composed traversal works" expected doubled

    -- Collect only present values using Fold.toListTraversal
    let collected := Fold.toListTraversal composed treeOfOptions
    ensureEq "Collected only present values" [5, 15] collected
}

/-- Test: Self-modifying recursive structure (mind-bending!) -/
private def case_selfModifyingTraversal : TestCase := {
  name := "Mind-bending: tree modifies itself - later nodes affected by earlier ones",
  run := do
    -- Create tree where traversal order matters
    -- Traversal visits: 5, 10, 15 (triggers!), 8, 3, 20, 2
    let tree := Rose.node 5 [
      Rose.node 10 [],
      Rose.node 15 [           -- This will trigger the "seen large" flag
        Rose.node 8 [],        -- These should be negated!
        Rose.node 3 []
      ],
      Rose.node 20 [           -- This stays positive (resets flag)
        Rose.node 2 []         -- This should be negated!
      ]
    ]

    -- Use direct Rose.walk for StateT traversal (works around compiler limitation)
    let tr : Traversal' (Rose Int) Int := traversal Rose.walk

    -- Strategy: Once we see a large value (>12), negate all subsequent small values
    -- Large values themselves stay positive but keep the negation flag active
    let modifyBasedOnPrevious (x : Int) : StateT Bool Id Int := do
      let shouldNegate ← get
      if x > 12 then
        set true   -- Turn on negation for subsequent small values
        pure x     -- But large values themselves aren't negated
      else if shouldNegate then
        pure (-x)  -- Negate small values when flag is on
      else
        pure x     -- Before first large value, keep unchanged

    let (result, _) := (Traversal.traverse' tr modifyBasedOnPrevious tree).run false

    -- Verify the self-modification worked
    -- Expected structure after transformation (traversal order: 5,10,15,8,3,20,2):
    -- 5 (unchanged - before any large value)
    -- 10 (unchanged - before any large value)
    -- 15 (large value - turns on negation, stays 15)
    -- 8 (negated → -8, negation is active)
    -- 3 (negated → -3, negation still active)
    -- 20 (large value - keeps negation on, stays 20)
    -- 2 (negated → -2, negation still active)

    match result with
    | Rose.node root children =>
      ensureEq "Root: unchanged (before large value)" 5 root

      match children with
      | [Rose.node v1 c1, Rose.node v2 c2, Rose.node v3 c3] =>
        ensureEq "Child 1: unchanged (before large value)" 10 v1
        ensure (c1.isEmpty) "Child 1 has no children"

        ensureEq "Child 2: large value activates negation" 15 v2
        match c2 with
        | [Rose.node v2_1 _, Rose.node v2_2 _] =>
          ensureEq "Grandchild 2.1: negated after parent" (-8) v2_1
          ensureEq "Grandchild 2.2: still negated" (-3) v2_2
        | _ => ensure false "Expected 2 grandchildren under child 2"

        ensureEq "Child 3: large value stays positive" 20 v3
        match c3 with
        | [Rose.node v3_1 _] =>
          ensureEq "Grandchild 3.1: negated after parent" (-2) v3_1
        | _ => ensure false "Expected 1 grandchild under child 3"

      | _ => ensure false "Expected 3 children"

    -- Key insight: The State monad threads through the ENTIRE recursive traversal!
    -- Earlier nodes can affect how later (even deeply nested) nodes are transformed.
    -- This is "self-modification" - the tree's own values determine its transformation.
}

/-- Test: Deep recursive tree with actual depth tracking -/
private def case_deepRecursiveTree : TestCase := {
  name := "Deep tree: track and transform based on actual recursion depth",
  run := do
    -- Build a deep binary tree with leaves at different depths:
    --           node (depth 0)
    --          /              \
    --       node              node (depth 1)
    --      /    \            /    \
    --   leaf(1) leaf(2)   node   leaf(5)
    --  depth 2  depth 2  depth 2 depth 2
    --                    /    \
    --                 leaf(3) leaf(4)
    --                depth 3  depth 3
    let deepTree : Tree Int := Tree.node
      (Tree.node
        (Tree.leaf 1)
        (Tree.leaf 2))
      (Tree.node
        (Tree.node
          (Tree.leaf 3)
          (Tree.leaf 4))
        (Tree.leaf 5))

    -- Transform: multiply value by (depth + 1)
    -- Leaves at depth 2: multiply by 3
    -- Leaves at depth 3: multiply by 4
    let transformWithDepth (depth : Nat) (x : Int) : Id Int :=
      x * ((depth + 1) : Int)

    let result := Tree.walkWithDepth transformWithDepth 0 deepTree

    -- Collect values to verify correct depth-based transformation
    let collectValues (depth : Nat) (x : Int) : StateT (List (Nat × Int)) Id Int := do
      modify ((depth, x) :: ·)
      pure x

    let (_, depthValuePairs) := (Tree.walkWithDepth collectValues 0 deepTree).run []

    -- Verify depths: leaves 1,2,5 at depth 2; leaves 3,4 at depth 3
    ensureEq "Depth-value pairs collected" [(2, 1), (2, 2), (3, 3), (3, 4), (2, 5)] depthValuePairs.reverse

    -- Verify transformations based on depth
    let collectTransformed (_depth : Nat) (x : Int) : StateT (List Int) Id Int := do
      modify (x :: ·)
      pure x

    let (_, transformedValues) := (Tree.walkWithDepth collectTransformed 0 result).run []

    -- Verify: 1*3=3, 2*3=6, 3*4=12, 4*4=16, 5*3=15
    ensureEq "Values transformed by depth multiplier" [3, 6, 12, 16, 15] transformedValues.reverse
}

/-! ## Plated Capabilities -/

/-- Test: Plated.transform for bottom-up tree rewriting -/
private def case_platedTransform : TestCase := {
  name := "Plated.transform: bottom-up tree simplification",
  run := do
    -- Build a tree with opportunities for simplification
    -- We'll simplify: node(leaf x, leaf x) -> leaf (x * 2)
    let tree : Tree Int := Tree.node
      (Tree.node (Tree.leaf 5) (Tree.leaf 5))    -- Can simplify to leaf 10
      (Tree.node
        (Tree.leaf 3)
        (Tree.node (Tree.leaf 7) (Tree.leaf 7))) -- Inner can simplify to leaf 14

    -- Bottom-up transform: combine identical sibling leaves
    let simplify (t : Tree Int) : Tree Int :=
      match t with
      | Tree.node (Tree.leaf x) (Tree.leaf y) =>
          if x == y then Tree.leaf (x * 2) else t
      | _ => t

    let simplified := transform simplify tree

    -- Expected: node(leaf 10, node(leaf 3, leaf 14))
    let expected := Tree.node
      (Tree.leaf 10)
      (Tree.node (Tree.leaf 3) (Tree.leaf 14))

    ensureEq "Bottom-up simplification" expected simplified
}

/-- Test: Plated.rewrite for iterative rewriting -/
private def case_platedRewrite : TestCase := {
  name := "Plated.rewrite: iterative expression simplification",
  run := do
    -- Build a deeply nested structure that can be flattened
    -- We'll use rose tree to represent a list-like structure
    -- node(1, [node(2, [node(3, [])])]) -> flattened form

    let nested : Rose Int := Rose.node 1 [
      Rose.node 2 [
        Rose.node 3 [
          Rose.node 4 []
        ]
      ]
    ]

    -- Rewrite rule: if a node has exactly one child, merge them
    -- node(x, [node(y, cs)]) -> node(x+y, cs)
    let flattenSingle (t : Rose Int) : Option (Rose Int) :=
      match t with
      | Rose.node x [Rose.node y cs] => some (Rose.node (x + y) cs)
      | _ => none

    let flattened := rewrite flattenSingle nested

    -- Expected: node(10, []) since 1+2+3+4 = 10
    let expected := Rose.node 10 []

    ensureEq "Iterative flattening" expected flattened
}

/-- Test: Using Plated utilities together -/
private def case_platedUtilities : TestCase := {
  name := "Plated utilities: universeList, findOf, anyOf",
  run := do
    let tree : Rose String := Rose.node "root" [
      Rose.node "child1" [
        Rose.node "grandchild1" [],
        Rose.node "target" []
      ],
      Rose.node "child2" []
    ]

    -- universeList collects all nodes
    let allNodes := universeList tree
    ensureEq "universeList count" 5 allNodes.length

    -- findOf finds first matching node
    let found := findOf (fun (t : Rose String) =>
      match t with
      | Rose.node "target" _ => true
      | _ => false) tree

    match found with
    | some (Rose.node v _) => ensureEq "findOf found target" "target" v
    | none => ensure false "Expected to find target"

    -- anyOf checks if any node matches
    let hasTarget := anyOf (fun (t : Rose String) =>
      match t with
      | Rose.node "target" _ => true
      | _ => false) tree
    ensure hasTarget "anyOf finds target"

    let hasMissing := anyOf (fun (t : Rose String) =>
      match t with
      | Rose.node "missing" _ => true
      | _ => false) tree
    ensure (!hasMissing) "anyOf correctly reports missing"
}

def cases : List TestCase := [
  case_binaryTreeTraversal,
  case_depthAwareTraversal,
  case_roseTreeTraversal,
  case_deeplyNestedRoseTree,
  case_recursiveValidation,
  case_recursiveStatefulTransform,
  case_composedRecursiveTraversal,
  case_selfModifyingTraversal,
  case_deepRecursiveTree,
  case_platedTransform,
  case_platedRewrite,
  case_platedUtilities
]

end CollimatorTests.AdvancedShowcase.MindBending
