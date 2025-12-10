/-!
# Indexed Optics Examples

This file demonstrates the use of indexed optics in Collimator.
Indexed optics provide access to both the position (index) and
value during traversal.

## Key Concepts

- `itraversed` - Indexed traversal returning `(index, value)` pairs
- `HasAt` - Typeclass for lens-based access at an index
- `HasIx` - Typeclass for traversal-based access at an index
- `ifilteredList` - Filter by both index and value

## When to Use Indexed Optics

Use indexed optics when you need to:
- Transform values based on their position
- Filter elements by their index
- Collect values along with their positions
- Access specific indices safely
-/

import Collimator.Prelude

open Collimator
open Collimator.Instances.List
open Collimator.Indexed

/-! ## Basic Indexed Traversal -/

/-- Access indices alongside values with itraversed. -/
example : List (Nat × String) :=
  -- itraversed returns (index, value) pairs
  let items := ["apple", "banana", "cherry"]
  Fold.toListTraversal itraversed items
  -- Result: [(0, "apple"), (1, "banana"), (2, "cherry")]

/-- Transform values using their index. -/
example : List String :=
  let items := ["a", "b", "c", "d"]
  -- Prefix each string with its index
  Traversal.over' itraversed (fun (i, s) => s!"{i}:{s}") items
  |>.map (·.2)  -- Extract just the strings
  -- Note: itraversed modifies pairs, so we map to extract strings
  -- Result: ["0:a", "1:b", "2:c", "3:d"]

/-! ## Filtering by Index -/

/-- Modify only elements at even indices. -/
example : List Int :=
  let nums := [10, 20, 30, 40, 50]
  Collimator.Combinators.Filtered.ifilteredList (fun i _ => i % 2 == 0)
    |> fun t => Traversal.over' t (· * 100) nums
  -- Result: [1000, 20, 3000, 40, 5000]

/-- Filter by both index and value. -/
example : List Int :=
  let nums := [5, 10, 15, 20, 25, 30]
  -- Keep only elements where index < value / 5
  Collimator.Combinators.Filtered.ifilteredList (fun i v => i < v / 5)
    |> fun t => Fold.toListTraversal t nums
  -- Elements: (0,5) -> 0 < 1 ✓, (1,10) -> 1 < 2 ✓, (2,15) -> 2 < 3 ✓,
  --           (3,20) -> 3 < 4 ✓, (4,25) -> 4 < 5 ✓, (5,30) -> 5 < 6 ✓
  -- Result: [5, 10, 15, 20, 25, 30] (all pass in this case)

/-! ## Safe Index Access with HasAt -/

/-- Lens-based access returns Option for safety. -/
example : Option String :=
  let items := ["first", "second", "third"]
  -- atLens gives a Lens to Option α
  view' (atLens 1) items
  -- Result: some "second"

example : Option String :=
  let items := ["first", "second", "third"]
  view' (atLens 10) items  -- Out of bounds
  -- Result: none

/-- Update at a specific index. -/
example : List String :=
  let items := ["a", "b", "c"]
  set' (atLens 1) (some "REPLACED") items
  -- Result: ["a", "REPLACED", "c"]

/-! ## Traversal-based Index Access with HasIx -/

/-- ix creates a traversal that focuses one element. -/
example : List Int :=
  let nums := [10, 20, 30, 40, 50]
  Traversal.over' (ix 2) (· + 1000) nums
  -- Result: [10, 20, 1030, 40, 50]

/-- Out-of-bounds ix is a no-op (empty traversal). -/
example : List Int :=
  let nums := [10, 20, 30]
  Traversal.over' (ix 100) (· + 1000) nums
  -- Result: [10, 20, 30] (unchanged)

/-! ## Composing Indexed Optics -/

/-- Nested access: index into a list of lists. -/
example : List (List Int) :=
  let matrix := [[1, 2, 3], [4, 5, 6], [7, 8, 9]]
  -- Modify element at row 1, column 2
  let rowLens := ix 1  -- Focus row at index 1
  let colLens := ix 2  -- Focus column at index 2
  -- Compose: first row, then column within that row
  Traversal.over' rowLens
    (fun row => Traversal.over' colLens (· * 100) row)
    matrix
  -- Result: [[1, 2, 3], [4, 5, 600], [7, 8, 9]]

/-! ## Practical Example: Numbered List -/

/-- Create a numbered list from items. -/
def numberItems (items : List String) : List String :=
  let pairs := Fold.toListTraversal itraversed items
  pairs.map fun (i, s) => s!"{i + 1}. {s}"

#eval numberItems ["Buy milk", "Walk dog", "Write code"]
-- ["1. Buy milk", "2. Walk dog", "3. Write code"]

/-! ## Practical Example: Alternating Styles -/

/-- Apply alternating transformations based on index. -/
def alternating (items : List String) : List String :=
  let indexed := Fold.toListTraversal itraversed items
  indexed.map fun (i, s) =>
    if i % 2 == 0 then s.toUpper else s.toLower

#eval alternating ["One", "Two", "Three", "Four"]
-- ["ONE", "two", "THREE", "four"]

/-! ## Key Differences: HasAt vs HasIx

| Feature | HasAt (atLens) | HasIx (ix) |
|---------|----------------|------------|
| Returns | `Lens' s (Option a)` | `Traversal' s a` |
| Type | Lens (always focuses) | Traversal (0-or-1 focus) |
| Get | `view'` returns `Option a` | Use `toListOf` |
| Set | Can set to `some v` or `none` | Only modifies if present |
| Missing | Returns `none` | Empty traversal (no-op) |

Use `HasAt` when you need to:
- Explicitly handle the "not found" case
- Possibly insert/remove elements

Use `HasIx` when you need to:
- Just modify if present, ignore if missing
- Compose with other traversals
-/
