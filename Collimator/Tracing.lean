import Collimator.Optics
import Collimator.Operators

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
open scoped Collimator.Operators

/-! ## Helper Functions -/

/-- Pad a string on the right with spaces to reach a minimum length -/
private def padRight (s : String) (len : Nat) : String :=
  if s.length >= len then s
  else s ++ String.ofList (List.replicate (len - s.length) ' ')

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

/-- Trace composition of a list of optic kinds, showing step-by-step reduction -/
def traceComposeKinds (kinds : List OpticType) : IO Unit := do
  match kinds with
  | [] =>
    IO.println "Empty composition"
  | [k] =>
    IO.println s!"{k}"
  | k :: ks =>
    -- Print the full chain
    let chainStr := String.intercalate " ⊚ " (kinds.map toString)
    IO.println chainStr
    -- Reduce and show final result
    let mut current := k
    for next in ks do
      current := composeOpticTypes current next
    IO.println s!"  = {current}"

/-- Trace composition of two optics -/
def traceCompose₂ {α β : Type 1} [OpticKind α] [OpticKind β]
    (o1 : α) (o2 : β) : IO Unit :=
  traceComposeKinds [opticKind o1, opticKind o2]

/-- Trace composition of three optics -/
def traceCompose₃ {α β γ : Type 1} [OpticKind α] [OpticKind β] [OpticKind γ]
    (o1 : α) (o2 : β) (o3 : γ) : IO Unit :=
  traceComposeKinds [opticKind o1, opticKind o2, opticKind o3]

/-- Trace composition of four optics -/
def traceCompose₄ {α β γ δ : Type 1} [OpticKind α] [OpticKind β] [OpticKind γ] [OpticKind δ]
    (o1 : α) (o2 : β) (o3 : γ) (o4 : δ) : IO Unit :=
  traceComposeKinds [opticKind o1, opticKind o2, opticKind o3, opticKind o4]

/-- Trace composition of five optics -/
def traceCompose₅ {α β γ δ ε : Type 1} [OpticKind α] [OpticKind β] [OpticKind γ] [OpticKind δ] [OpticKind ε]
    (o1 : α) (o2 : β) (o3 : γ) (o4 : δ) (o5 : ε) : IO Unit :=
  traceComposeKinds [opticKind o1, opticKind o2, opticKind o3, opticKind o4, opticKind o5]

/-- Trace composition using variadic syntax: traceCompose![lens1, trav, lens2] -/
syntax "traceCompose![" term,* "]" : term

macro_rules
  | `(traceCompose![$o1:term, $o2:term]) =>
    `(traceCompose₂ $o1 $o2)
  | `(traceCompose![$o1:term, $o2:term, $o3:term]) =>
    `(traceCompose₃ $o1 $o2 $o3)
  | `(traceCompose![$o1:term, $o2:term, $o3:term, $o4:term]) =>
    `(traceCompose₄ $o1 $o2 $o3 $o4)
  | `(traceCompose![$o1:term, $o2:term, $o3:term, $o4:term, $o5:term]) =>
    `(traceCompose₅ $o1 $o2 $o3 $o4 $o5)

/-! ## Tracing with Normal Composition Syntax

The `trace!` macro lets you write normal composition expressions and get tracing output.
It parses the `⊚` chain, prints the composition trace, and returns the composed optic.

```lean
-- Instead of: traceCompose![lens1, trav, lens2]
-- Write:      trace! lens1 ⊚ trav ⊚ lens2

def myOptic := trace! addressLens ⊚ cityLens  -- prints trace, returns Lens
```
-/

/-- Trace and return: prints composition info, then returns the composed optic -/
def traceAndReturn₂ {α β γ : Type 1} [OpticKind α] [OpticKind β]
    (o1 : α) (o2 : β) (composed : γ) : γ :=
  let k1 := opticKind o1
  let k2 := opticKind o2
  let result := composeOpticTypes k1 k2
  dbg_trace s!"{k1} ⊚ {k2} = {result}"
  composed

def traceAndReturn₃ {α β γ δ : Type 1} [OpticKind α] [OpticKind β] [OpticKind γ]
    (o1 : α) (o2 : β) (o3 : γ) (composed : δ) : δ :=
  let k1 := opticKind o1
  let k2 := opticKind o2
  let k3 := opticKind o3
  let r1 := composeOpticTypes k1 k2
  let result := composeOpticTypes r1 k3
  dbg_trace s!"{k1} ⊚ {k2} ⊚ {k3} = {result}"
  composed

def traceAndReturn₄ {α β γ δ ε : Type 1} [OpticKind α] [OpticKind β] [OpticKind γ] [OpticKind δ]
    (o1 : α) (o2 : β) (o3 : γ) (o4 : δ) (composed : ε) : ε :=
  let k1 := opticKind o1
  let k2 := opticKind o2
  let k3 := opticKind o3
  let k4 := opticKind o4
  let r1 := composeOpticTypes k1 k2
  let r2 := composeOpticTypes r1 k3
  let result := composeOpticTypes r2 k4
  dbg_trace s!"{k1} ⊚ {k2} ⊚ {k3} ⊚ {k4} = {result}"
  composed

def traceAndReturn₅ {α β γ δ ε ζ : Type 1} [OpticKind α] [OpticKind β] [OpticKind γ] [OpticKind δ] [OpticKind ε]
    (o1 : α) (o2 : β) (o3 : γ) (o4 : δ) (o5 : ε) (composed : ζ) : ζ :=
  let k1 := opticKind o1
  let k2 := opticKind o2
  let k3 := opticKind o3
  let k4 := opticKind o4
  let k5 := opticKind o5
  let r1 := composeOpticTypes k1 k2
  let r2 := composeOpticTypes r1 k3
  let r3 := composeOpticTypes r2 k4
  let result := composeOpticTypes r3 k5
  dbg_trace s!"{k1} ⊚ {k2} ⊚ {k3} ⊚ {k4} ⊚ {k5} = {result}"
  composed

/--
Trace a composition expression using `trace![]` syntax with comma-separated optics.
Prints composition info and returns the composed optic.

```lean
-- Traces "Lens ⊚ Lens = Lens" and returns the composed lens
def myLens := trace![addressLens, cityLens]

-- Works with heterogeneous composition too
def myTrav := trace![deptLens, traversed, empLens]
```
-/

syntax "trace![" term ", " term "]" : term
syntax "trace![" term ", " term ", " term "]" : term
syntax "trace![" term ", " term ", " term ", " term "]" : term
syntax "trace![" term ", " term ", " term ", " term ", " term "]" : term

macro_rules
  | `(trace![$o1, $o2]) =>
    `(traceAndReturn₂ $o1 $o2 ($o1 ∘ $o2))
  | `(trace![$o1, $o2, $o3]) =>
    `(traceAndReturn₃ $o1 $o2 $o3 ($o1 ∘ $o2 ∘ $o3))
  | `(trace![$o1, $o2, $o3, $o4]) =>
    `(traceAndReturn₄ $o1 $o2 $o3 $o4 ($o1 ∘ $o2 ∘ $o3 ∘ $o4))
  | `(trace![$o1, $o2, $o3, $o4, $o5]) =>
    `(traceAndReturn₅ $o1 $o2 $o3 $o4 $o5 ($o1 ∘ $o2 ∘ $o3 ∘ $o4 ∘ $o5))

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
