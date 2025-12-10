import Collimator.Optics.Types

/-!
# Optic Composition Tracing

Utilities for understanding and debugging optic compositions.

## Features

- `describeOptic`: Get a human-readable description of an optic type
- `traceComposition`: Show the type flow through a composition chain
- `opticCapabilities`: List what operations an optic supports

## Usage

```lean
import Collimator.Tracing

-- Describe what type of optic you have
#eval IO.println (describeOptic "Lens")

-- Show composition chain
#eval traceComposition [("companyLens", "Lens"), ("deptTraversal", "Traversal"), ("empLens", "Lens")]
```
-/

namespace Collimator.Tracing

/-! ## Helper Functions -/

/-- Pad a string on the right with spaces to reach a minimum length -/
private def padRight (s : String) (len : Nat) : String :=
  if s.length >= len then s
  else s ++ String.mk (List.replicate (len - s.length) ' ')

/-! ## Optic Type Descriptions -/

/-- Human-readable description of each optic type -/
def describeOptic (opticType : String) : String :=
  match opticType with
  | "Iso" =>
    "Iso (Isomorphism)\n" ++
    "  Focus: Exactly one, bidirectional\n" ++
    "  Use case: Type-safe bidirectional transformations\n" ++
    "  Operations: view, set, over, preview (always Some), review, traverse\n" ++
    "  Example: String ↔ List Char"
  | "Lens" =>
    "Lens\n" ++
    "  Focus: Exactly one part of a product\n" ++
    "  Use case: Accessing/modifying fields in structures\n" ++
    "  Operations: view, set, over, preview (always Some), traverse\n" ++
    "  Example: Person → name field"
  | "Prism" =>
    "Prism\n" ++
    "  Focus: Zero or one (one case of a sum type)\n" ++
    "  Use case: Working with variants/constructors\n" ++
    "  Operations: preview (may be None), review, set, over, traverse\n" ++
    "  Example: Option α → Some case"
  | "AffineTraversal" =>
    "AffineTraversal\n" ++
    "  Focus: Zero or one\n" ++
    "  Use case: Optional access (Lens ∘ Prism)\n" ++
    "  Operations: preview, set, over, traverse\n" ++
    "  Example: Safe head of a list"
  | "Traversal" =>
    "Traversal\n" ++
    "  Focus: Zero or more\n" ++
    "  Use case: Batch operations on collections\n" ++
    "  Operations: set, over, traverse (no view!)\n" ++
    "  Example: All elements of a list"
  | "Fold" =>
    "Fold\n" ++
    "  Focus: Zero or more (read-only)\n" ++
    "  Use case: Aggregating/collecting values\n" ++
    "  Operations: toList, foldMap (read-only)\n" ++
    "  Example: Collecting all names in a tree"
  | "Setter" =>
    "Setter\n" ++
    "  Focus: Zero or more (write-only)\n" ++
    "  Use case: Batch updates without reading\n" ++
    "  Operations: set, over (write-only)\n" ++
    "  Example: Setting all elements to a value"
  | "Getter" =>
    "Getter\n" ++
    "  Focus: Exactly one (read-only)\n" ++
    "  Use case: Computed/derived values\n" ++
    "  Operations: view (read-only)\n" ++
    "  Example: Full name from first + last"
  | "Review" =>
    "Review\n" ++
    "  Focus: Construction only (write-only)\n" ++
    "  Use case: Smart constructors\n" ++
    "  Operations: review (construct-only)\n" ++
    "  Example: Building Option from value"
  | _ => s!"Unknown optic type: {opticType}"

/-! ## Capability Matrix -/

/-- Operations supported by each optic type -/
structure OpticCapabilities where
  view : Bool
  set : Bool
  over : Bool
  preview : Bool
  review : Bool
  traverse : Bool
  toList : Bool
deriving Repr

def getCapabilities (opticType : String) : OpticCapabilities :=
  match opticType with
  | "Iso" => ⟨true, true, true, true, true, true, true⟩
  | "Lens" => ⟨true, true, true, true, false, true, true⟩
  | "Prism" => ⟨false, true, true, true, true, true, true⟩
  | "AffineTraversal" => ⟨false, true, true, true, false, true, true⟩
  | "Traversal" => ⟨false, true, true, false, false, true, true⟩
  | "Fold" => ⟨false, false, false, false, false, false, true⟩
  | "Setter" => ⟨false, true, true, false, false, false, false⟩
  | "Getter" => ⟨true, false, false, false, false, false, false⟩
  | "Review" => ⟨false, false, false, false, true, false, false⟩
  | _ => ⟨false, false, false, false, false, false, false⟩

def capabilitiesToString (caps : OpticCapabilities) : String :=
  let ops := #[
    ("view", caps.view),
    ("set", caps.set),
    ("over", caps.over),
    ("preview", caps.preview),
    ("review", caps.review),
    ("traverse", caps.traverse),
    ("toList", caps.toList)
  ]
  let supported := ops.filter (·.2) |>.map (·.1)
  String.intercalate ", " supported.toList

/-- Print capabilities for an optic type -/
def printCapabilities (opticType : String) : IO Unit := do
  let caps := getCapabilities opticType
  IO.println s!"{opticType} supports: {capabilitiesToString caps}"

/-! ## Composition Rules -/

/-- Determine the result type when composing two optics -/
def composeTypes (outer inner : String) : String :=
  match outer, inner with
  -- Iso composes to the inner type
  | "Iso", t => t
  | t, "Iso" => t
  -- Lens compositions
  | "Lens", "Lens" => "Lens"
  | "Lens", "Prism" => "AffineTraversal"
  | "Lens", "AffineTraversal" => "AffineTraversal"
  | "Lens", "Traversal" => "Traversal"
  | "Lens", "Fold" => "Fold"
  | "Lens", "Setter" => "Setter"
  | "Lens", "Getter" => "Getter"
  -- Prism compositions
  | "Prism", "Lens" => "AffineTraversal"
  | "Prism", "Prism" => "Prism"
  | "Prism", "AffineTraversal" => "AffineTraversal"
  | "Prism", "Traversal" => "Traversal"
  | "Prism", "Fold" => "Fold"
  | "Prism", "Setter" => "Setter"
  -- AffineTraversal compositions
  | "AffineTraversal", "Lens" => "AffineTraversal"
  | "AffineTraversal", "Prism" => "AffineTraversal"
  | "AffineTraversal", "AffineTraversal" => "AffineTraversal"
  | "AffineTraversal", "Traversal" => "Traversal"
  | "AffineTraversal", "Fold" => "Fold"
  | "AffineTraversal", "Setter" => "Setter"
  -- Traversal compositions
  | "Traversal", "Lens" => "Traversal"
  | "Traversal", "Prism" => "Traversal"
  | "Traversal", "AffineTraversal" => "Traversal"
  | "Traversal", "Traversal" => "Traversal"
  | "Traversal", "Fold" => "Fold"
  | "Traversal", "Setter" => "Setter"
  -- Fold compositions
  | "Fold", "Lens" => "Fold"
  | "Fold", "Prism" => "Fold"
  | "Fold", "AffineTraversal" => "Fold"
  | "Fold", "Traversal" => "Fold"
  | "Fold", "Fold" => "Fold"
  | "Fold", "Getter" => "Fold"
  -- Getter compositions
  | "Getter", "Lens" => "Getter"
  | "Getter", "Getter" => "Getter"
  -- Setter compositions
  | "Setter", "Lens" => "Setter"
  | "Setter", "Prism" => "Setter"
  | "Setter", "AffineTraversal" => "Setter"
  | "Setter", "Traversal" => "Setter"
  | "Setter", "Setter" => "Setter"
  -- Default
  | a, b => s!"({a} ∘ {b})"

/-! ## Composition Tracing -/

/--
Trace a composition chain, showing the resulting type at each step.

Input: List of (name, optic_type) pairs in composition order
Output: Formatted string showing the composition flow
-/
def traceComposition (chain : List (String × String)) : IO Unit := do
  if chain.isEmpty then
    IO.println "Empty composition chain"
    return

  IO.println "Composition trace:"
  IO.println "─────────────────"

  let mut currentType := ""
  let mut isFirst := true

  for (name, opticType) in chain do
    if isFirst then
      IO.println s!"  {name} : {opticType}"
      currentType := opticType
      isFirst := false
    else
      let newType := composeTypes currentType opticType
      IO.println s!"    ⊚"
      IO.println s!"  {name} : {opticType}"
      IO.println s!"    → result: {newType}"
      currentType := newType

  IO.println "─────────────────"
  IO.println s!"Final type: {currentType}"
  IO.println ""

  let caps := getCapabilities currentType
  IO.println s!"Supported operations: {capabilitiesToString caps}"

/--
Print a quick reference for optic composition results.
-/
def printCompositionMatrix : IO Unit := do
  let types := ["Iso", "Lens", "Prism", "AffineTraversal", "Traversal"]

  IO.println "Optic Composition Matrix"
  IO.println "========================"
  IO.println ""
  IO.println "outer \\ inner | Iso    Lens   Prism  Affine Trav"
  IO.println "--------------+------------------------------------"

  for outer in types do
    let abbrevOuter := match outer with
      | "AffineTraversal" => "Affine"
      | "Traversal" => "Trav"
      | x => x
    let row := types.map fun inner =>
      let result := composeTypes outer inner
      match result with
      | "AffineTraversal" => "Affine"
      | "Traversal" => "Trav"
      | x => padRight x 6
    IO.println s!"{padRight abbrevOuter 13} | {String.intercalate " " row}"

/-! ## Optic Information -/

/--
Print comprehensive information about an optic type.
-/
def printOpticInfo (opticType : String) : IO Unit := do
  IO.println "========================================"
  IO.println s!"Optic: {opticType}"
  IO.println "========================================"
  IO.println ""
  IO.println (describeOptic opticType)
  IO.println ""

  let caps := getCapabilities opticType
  IO.println "Capability Matrix:"
  IO.println s!"  view:     {if caps.view then "✓" else "✗"}"
  IO.println s!"  set:      {if caps.set then "✓" else "✗"}"
  IO.println s!"  over:     {if caps.over then "✓" else "✗"}"
  IO.println s!"  preview:  {if caps.preview then "✓" else "✗"}"
  IO.println s!"  review:   {if caps.review then "✓" else "✗"}"
  IO.println s!"  traverse: {if caps.traverse then "✓" else "✗"}"
  IO.println s!"  toList:   {if caps.toList then "✓" else "✗"}"

end Collimator.Tracing
