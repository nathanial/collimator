import Collimator.Prelude

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

open Collimator
open Collimator.Instances.List  -- For traversed, itraversed
open Collimator.Indexed         -- For HasAt, HasIx
open scoped Collimator.Operators

/-! ## Basic Indexed Traversal -/

/-- Access indices alongside values with itraversed. -/
example : List (Nat × String) :=
  -- itraversed returns (index, value) pairs
  let items := ["apple", "banana", "cherry"]
  items ^.. itraversed
  -- Result: [(0, "apple"), (1, "banana"), (2, "cherry")]

/-- Transform values using their index.
    Note: itraversed works on (Nat × α) pairs -/
def indexedPrefix (items : List String) : List String :=
  let indexed := items ^.. itraversed
  indexed.map fun (i, s) => s!"{i}:{s}"

#eval indexedPrefix ["a", "b", "c", "d"]
-- ["0:a", "1:b", "2:c", "3:d"]

/-! ## Filtering by Index -/

/-- Modify only elements at even indices. -/
example : List Int :=
  let nums := [10, 20, 30, 40, 50]
  nums & ifilteredList (fun i _ => i % 2 == 0) %~ (· * 100)
  -- Result: [1000, 20, 3000, 40, 5000]

/-- Filter by both index and value. -/
example : List Nat :=
  let nums := [5, 10, 15, 20, 25, 30]
  -- Keep only elements where index < value / 5
  nums ^.. ifilteredList (fun i v => decide (i < v / 5))
  -- Elements: (0,5) -> 0 < 1 ✓, (1,10) -> 1 < 2 ✓, (2,15) -> 2 < 3 ✓,
  --           (3,20) -> 3 < 4 ✓, (4,25) -> 4 < 5 ✓, (5,30) -> 5 < 6 ✓
  -- Result: [5, 10, 15, 20, 25, 30] (all pass in this case)

/-! ## Safe Index Access with HasAt -/

/-- Lens-based access returns Option for safety. -/
example : Option String :=
  let items := ["first", "second", "third"]
  -- atLens gives a Lens to Option α
  items ^. atLens 1
  -- Result: some "second"

example : Option String :=
  let items := ["first", "second", "third"]
  items ^. atLens 10  -- Out of bounds
  -- Result: none

/-- Update at a specific index. -/
example : List String :=
  let items := ["a", "b", "c"]
  items & atLens 1 .~ some "REPLACED"
  -- Result: ["a", "REPLACED", "c"]

/-! ## Traversal-based Index Access with HasIx -/

/-- ix creates a traversal that focuses one element. -/
example : List Int :=
  let nums : List Int := [10, 20, 30, 40, 50]
  nums & ix (s := List Int) (a := Int) 2 %~ (· + 1000)
  -- Result: [10, 20, 1030, 40, 50]

/-- Out-of-bounds ix is a no-op (empty traversal). -/
example : List Int :=
  let nums : List Int := [10, 20, 30]
  nums & ix (s := List Int) (a := Int) 100 %~ (· + 1000)
  -- Result: [10, 20, 30] (unchanged)

/-! ## Composing Indexed Optics -/

/-- Nested access: index into a list of lists. -/
example : List (List Int) :=
  let matrix : List (List Int) := [[1, 2, 3], [4, 5, 6], [7, 8, 9]]
  -- Modify element at row 1, column 2
  let rowTrav : Traversal' (List (List Int)) (List Int) := ix 1  -- Focus row at index 1
  let colTrav : Traversal' (List Int) Int := ix 2               -- Focus column at index 2
  -- Compose: first row, then column within that row
  matrix & rowTrav %~ (fun row => row & colTrav %~ (· * 100))
  -- Result: [[1, 2, 3], [4, 5, 600], [7, 8, 9]]

/-! ## Practical Example: Numbered List -/

/-- Create a numbered list from items. -/
def numberItems (items : List String) : List String :=
  let pairs := items ^.. itraversed
  pairs.map fun (i, s) => s!"{i + 1}. {s}"

#eval numberItems ["Buy milk", "Walk dog", "Write code"]
-- ["1. Buy milk", "2. Walk dog", "3. Write code"]

/-! ## Practical Example: Alternating Styles -/

/-- Apply alternating transformations based on index. -/
def alternating (items : List String) : List String :=
  let indexed := items ^.. itraversed
  indexed.map fun (i, s) =>
    if i % 2 == 0 then s.toUpper else s.toLower

#eval alternating ["One", "Two", "Three", "Four"]
-- ["ONE", "two", "THREE", "four"]

/-! ## Key Differences: HasAt vs HasIx

| Feature | HasAt (atLens) | HasIx (ix) |
|---------|----------------|------------|
| Returns | `Lens' s (Option a)` | `Traversal' s a` |
| Type | Lens (always focuses) | Traversal (0-or-1 focus) |
| Get | `^.` returns `Option a` | Use `^..` |
| Set | Can set to `some v` or `none` | Only modifies if present |
| Missing | Returns `none` | Empty traversal (no-op) |

Use `HasAt` when you need to:
- Explicitly handle the "not found" case
- Possibly insert/remove elements

Use `HasIx` when you need to:
- Just modify if present, ignore if missing
- Compose with other traversals
-/
