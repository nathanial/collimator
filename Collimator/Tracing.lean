import Collimator.Optics.Types

/-!
# Optic Composition Tracing

Utilities for understanding and debugging optic compositions.

## Features

- `OpticKind`: Typeclass to identify optic types at compile time
- `traceCompose`: Show the composition result of actual optics
- `describeOptic`: Get a human-readable description of an optic type
- `opticCapabilities`: List what operations an optic supports

## Usage

```lean
import Collimator.Tracing
import Collimator.Prelude

-- Get the kind of an actual optic
#eval IO.println (opticKind (lens' (·.1) (fun p v => (v, p.2)) : Lens' (Int × Int) Int))

-- Trace composition of actual optics
#eval traceCompose₂ myLens myTraversal
```
-/

namespace Collimator.Tracing

open Collimator

/-! ## Helper Functions -/

/-- Pad a string on the right with spaces to reach a minimum length -/
private def padRight (s : String) (len : Nat) : String :=
  if s.length >= len then s
  else s ++ String.mk (List.replicate (len - s.length) ' ')

/-! ## Optic Kind Identification -/

/-- Enumeration of optic kinds -/
inductive OpticType where
  | iso
  | lens
  | prism
  | affineTraversal
  | traversal
  | fold
  | setter
  | getter
  | review
  | unknown
deriving Repr, BEq

instance : ToString OpticType where
  toString
    | .iso => "Iso"
    | .lens => "Lens"
    | .prism => "Prism"
    | .affineTraversal => "AffineTraversal"
    | .traversal => "Traversal"
    | .fold => "Fold"
    | .setter => "Setter"
    | .getter => "Getter"
    | .review => "Review"
    | .unknown => "Unknown"

/-- Typeclass for identifying the kind of an optic -/
class OpticKind (α : Type 1) where
  kind : OpticType

instance : OpticKind (Iso s t a b) where kind := .iso
instance : OpticKind (Lens s t a b) where kind := .lens
instance : OpticKind (Prism s t a b) where kind := .prism
instance : OpticKind (AffineTraversal s t a b) where kind := .affineTraversal
instance : OpticKind (Traversal s t a b) where kind := .traversal
instance : OpticKind (Fold s t a b) where kind := .fold
instance : OpticKind (Setter s t a b) where kind := .setter

/-- Get the kind of an optic -/
def opticKind {α : Type 1} [OpticKind α] (_optic : α) : OpticType :=
  OpticKind.kind (α := α)

/-- Get the kind name as a string -/
def opticKindName {α : Type 1} [OpticKind α] (optic : α) : String :=
  toString (opticKind optic)

/-! ## Optic Type Descriptions -/

/-- Human-readable description of each optic type -/
def describeOpticType (t : OpticType) : String :=
  match t with
  | .iso =>
    "Iso (Isomorphism)\n" ++
    "  Focus: Exactly one, bidirectional\n" ++
    "  Use case: Type-safe bidirectional transformations\n" ++
    "  Operations: view, set, over, preview (always Some), review, traverse\n" ++
    "  Example: String ↔ List Char"
  | .lens =>
    "Lens\n" ++
    "  Focus: Exactly one part of a product\n" ++
    "  Use case: Accessing/modifying fields in structures\n" ++
    "  Operations: view, set, over, preview (always Some), traverse\n" ++
    "  Example: Person → name field"
  | .prism =>
    "Prism\n" ++
    "  Focus: Zero or one (one case of a sum type)\n" ++
    "  Use case: Working with variants/constructors\n" ++
    "  Operations: preview (may be None), review, set, over, traverse\n" ++
    "  Example: Option α → Some case"
  | .affineTraversal =>
    "AffineTraversal\n" ++
    "  Focus: Zero or one\n" ++
    "  Use case: Optional access (Lens ∘ Prism)\n" ++
    "  Operations: preview, set, over, traverse\n" ++
    "  Example: Safe head of a list"
  | .traversal =>
    "Traversal\n" ++
    "  Focus: Zero or more\n" ++
    "  Use case: Batch operations on collections\n" ++
    "  Operations: set, over, traverse (no view!)\n" ++
    "  Example: All elements of a list"
  | .fold =>
    "Fold\n" ++
    "  Focus: Zero or more (read-only)\n" ++
    "  Use case: Aggregating/collecting values\n" ++
    "  Operations: toList, foldMap (read-only)\n" ++
    "  Example: Collecting all names in a tree"
  | .setter =>
    "Setter\n" ++
    "  Focus: Zero or more (write-only)\n" ++
    "  Use case: Batch updates without reading\n" ++
    "  Operations: set, over (write-only)\n" ++
    "  Example: Setting all elements to a value"
  | .getter =>
    "Getter\n" ++
    "  Focus: Exactly one (read-only)\n" ++
    "  Use case: Computed/derived values\n" ++
    "  Operations: view (read-only)\n" ++
    "  Example: Full name from first + last"
  | .review =>
    "Review\n" ++
    "  Focus: Construction only (write-only)\n" ++
    "  Use case: Smart constructors\n" ++
    "  Operations: review (construct-only)\n" ++
    "  Example: Building Option from value"
  | .unknown => "Unknown optic type"

/-- Human-readable description by string name (for backwards compatibility) -/
def describeOptic (opticType : String) : String :=
  match opticType with
  | "Iso" => describeOpticType .iso
  | "Lens" => describeOpticType .lens
  | "Prism" => describeOpticType .prism
  | "AffineTraversal" => describeOpticType .affineTraversal
  | "Traversal" => describeOpticType .traversal
  | "Fold" => describeOpticType .fold
  | "Setter" => describeOpticType .setter
  | "Getter" => describeOpticType .getter
  | "Review" => describeOpticType .review
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

def getCapabilitiesForType (t : OpticType) : OpticCapabilities :=
  match t with
  | .iso => ⟨true, true, true, true, true, true, true⟩
  | .lens => ⟨true, true, true, true, false, true, true⟩
  | .prism => ⟨false, true, true, true, true, true, true⟩
  | .affineTraversal => ⟨false, true, true, true, false, true, true⟩
  | .traversal => ⟨false, true, true, false, false, true, true⟩
  | .fold => ⟨false, false, false, false, false, false, true⟩
  | .setter => ⟨false, true, true, false, false, false, false⟩
  | .getter => ⟨true, false, false, false, false, false, false⟩
  | .review => ⟨false, false, false, false, true, false, false⟩
  | .unknown => ⟨false, false, false, false, false, false, false⟩

def getCapabilities (opticType : String) : OpticCapabilities :=
  match opticType with
  | "Iso" => getCapabilitiesForType .iso
  | "Lens" => getCapabilitiesForType .lens
  | "Prism" => getCapabilitiesForType .prism
  | "AffineTraversal" => getCapabilitiesForType .affineTraversal
  | "Traversal" => getCapabilitiesForType .traversal
  | "Fold" => getCapabilitiesForType .fold
  | "Setter" => getCapabilitiesForType .setter
  | "Getter" => getCapabilitiesForType .getter
  | "Review" => getCapabilitiesForType .review
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
def composeOpticTypes (outer inner : OpticType) : OpticType :=
  match outer, inner with
  -- Iso composes to the inner type
  | .iso, t => t
  | t, .iso => t
  -- Lens compositions
  | .lens, .lens => .lens
  | .lens, .prism => .affineTraversal
  | .lens, .affineTraversal => .affineTraversal
  | .lens, .traversal => .traversal
  | .lens, .fold => .fold
  | .lens, .setter => .setter
  | .lens, .getter => .getter
  -- Prism compositions
  | .prism, .lens => .affineTraversal
  | .prism, .prism => .prism
  | .prism, .affineTraversal => .affineTraversal
  | .prism, .traversal => .traversal
  | .prism, .fold => .fold
  | .prism, .setter => .setter
  -- AffineTraversal compositions
  | .affineTraversal, .lens => .affineTraversal
  | .affineTraversal, .prism => .affineTraversal
  | .affineTraversal, .affineTraversal => .affineTraversal
  | .affineTraversal, .traversal => .traversal
  | .affineTraversal, .fold => .fold
  | .affineTraversal, .setter => .setter
  -- Traversal compositions
  | .traversal, .lens => .traversal
  | .traversal, .prism => .traversal
  | .traversal, .affineTraversal => .traversal
  | .traversal, .traversal => .traversal
  | .traversal, .fold => .fold
  | .traversal, .setter => .setter
  -- Fold compositions
  | .fold, .lens => .fold
  | .fold, .prism => .fold
  | .fold, .affineTraversal => .fold
  | .fold, .traversal => .fold
  | .fold, .fold => .fold
  | .fold, .getter => .fold
  -- Getter compositions
  | .getter, .lens => .getter
  | .getter, .getter => .getter
  -- Setter compositions
  | .setter, .lens => .setter
  | .setter, .prism => .setter
  | .setter, .affineTraversal => .setter
  | .setter, .traversal => .setter
  | .setter, .setter => .setter
  -- Default
  | _, _ => .unknown

/-- String version for backwards compatibility -/
def composeTypes (outer inner : String) : String :=
  let outerT := match outer with
    | "Iso" => OpticType.iso
    | "Lens" => .lens
    | "Prism" => .prism
    | "AffineTraversal" => .affineTraversal
    | "Traversal" => .traversal
    | "Fold" => .fold
    | "Setter" => .setter
    | "Getter" => .getter
    | "Review" => .review
    | _ => .unknown
  let innerT := match inner with
    | "Iso" => OpticType.iso
    | "Lens" => .lens
    | "Prism" => .prism
    | "AffineTraversal" => .affineTraversal
    | "Traversal" => .traversal
    | "Fold" => .fold
    | "Setter" => .setter
    | "Getter" => .getter
    | "Review" => .review
    | _ => .unknown
  toString (composeOpticTypes outerT innerT)

/-! ## Type-Safe Composition Tracing -/

/-- Trace composition of two optics, returning the result type -/
def traceCompose₂ {α β : Type 1} [OpticKind α] [OpticKind β]
    (o1 : α) (o2 : β) : IO OpticType := do
  let k1 := opticKind o1
  let k2 := opticKind o2
  let result := composeOpticTypes k1 k2
  IO.println s!"{k1} ⊚ {k2} = {result}"
  return result

/-- Trace composition of three optics -/
def traceCompose₃ {α β γ : Type 1} [OpticKind α] [OpticKind β] [OpticKind γ]
    (o1 : α) (o2 : β) (o3 : γ) : IO OpticType := do
  let k1 := opticKind o1
  let k2 := opticKind o2
  let k3 := opticKind o3
  let r1 := composeOpticTypes k1 k2
  let r2 := composeOpticTypes r1 k3
  IO.println s!"{k1} ⊚ {k2} ⊚ {k3}"
  IO.println s!"  = {r1} ⊚ {k3}"
  IO.println s!"  = {r2}"
  return r2

/-- Trace composition of four optics -/
def traceCompose₄ {α β γ δ : Type 1} [OpticKind α] [OpticKind β] [OpticKind γ] [OpticKind δ]
    (o1 : α) (o2 : β) (o3 : γ) (o4 : δ) : IO OpticType := do
  let k1 := opticKind o1
  let k2 := opticKind o2
  let k3 := opticKind o3
  let k4 := opticKind o4
  let r1 := composeOpticTypes k1 k2
  let r2 := composeOpticTypes r1 k3
  let r3 := composeOpticTypes r2 k4
  IO.println s!"{k1} ⊚ {k2} ⊚ {k3} ⊚ {k4}"
  IO.println s!"  = {r1} ⊚ {k3} ⊚ {k4}"
  IO.println s!"  = {r2} ⊚ {k4}"
  IO.println s!"  = {r3}"
  return r3

/-- Trace composition of five optics -/
def traceCompose₅ {α β γ δ ε : Type 1} [OpticKind α] [OpticKind β] [OpticKind γ] [OpticKind δ] [OpticKind ε]
    (o1 : α) (o2 : β) (o3 : γ) (o4 : δ) (o5 : ε) : IO OpticType := do
  let k1 := opticKind o1
  let k2 := opticKind o2
  let k3 := opticKind o3
  let k4 := opticKind o4
  let k5 := opticKind o5
  let r1 := composeOpticTypes k1 k2
  let r2 := composeOpticTypes r1 k3
  let r3 := composeOpticTypes r2 k4
  let r4 := composeOpticTypes r3 k5
  IO.println s!"{k1} ⊚ {k2} ⊚ {k3} ⊚ {k4} ⊚ {k5}"
  IO.println s!"  = {r1} ⊚ {k3} ⊚ {k4} ⊚ {k5}"
  IO.println s!"  = {r2} ⊚ {k4} ⊚ {k5}"
  IO.println s!"  = {r3} ⊚ {k5}"
  IO.println s!"  = {r4}"
  return r4

/-- Describe an optic with its kind -/
def describeOpticInstance {α : Type 1} [OpticKind α] (optic : α) : IO Unit := do
  let k := opticKind optic
  IO.println (describeOpticType k)
  IO.println ""
  let caps := getCapabilitiesForType k
  IO.println s!"Supported operations: {capabilitiesToString caps}"

/-! ## Legacy String-Based Tracing (for backwards compatibility) -/

/--
Trace a composition chain, showing the resulting type at each step.
(Legacy version using strings - prefer traceCompose₂, traceCompose₃, etc.)

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
  IO.println "When you compose (outer ⊚ inner), the result type is:"
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
