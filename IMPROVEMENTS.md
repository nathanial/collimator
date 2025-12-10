# Collimator Improvement Ideas

This document outlines potential improvements to make the Collimator optics library more usable and useful for Lean 4 developers.

## Current Strengths

Before diving into improvements, it's worth noting what's already working well:

- **Sound implementation**: All optics correctly implement profunctor laws with formal proofs
- **Comprehensive type coverage**: Iso, Lens, Prism, AffineTraversal, Traversal, Fold, Setter, Getter, Review
- **Two API styles**: Monomorphic (`view'`, `over'`) and polymorphic (`view`, `over`) for different use cases
- **Good composition**: The `⊚` operator and `Composable` typeclass work well
- **Operator syntax**: View (`^.`), preview (`^?`), set (`.~`), over (`%~`) operators available
- **Extensive test suite**: 221 tests covering laws, edge cases, and advanced patterns

---

## Priority 1: Documentation & Onboarding

### 1.1 Getting Started Tutorial

Create `docs/tutorial.md` with a progressive tutorial:

```markdown
1. Your First Lens (5 min)
   - Define a Point structure
   - Create x and y lenses manually
   - Use view, set, over

2. Composing Optics (10 min)
   - Nested structures (Company → Department → Employee)
   - The ⊚ operator
   - Type inference and when to add annotations

3. Working with Optional Data (10 min)
   - Prisms for sum types
   - preview and review
   - Composing lenses with prisms

4. Traversing Collections (10 min)
   - traversed for lists
   - Effectful traversals with Option/IO
   - Collecting results with folds

5. Real-World Patterns (15 min)
   - JSON-like data manipulation
   - Configuration updates
   - Validation pipelines
```

### 1.2 Quick Reference Cheat Sheet

Create `docs/cheatsheet.md`:

| Operation | Monomorphic | Polymorphic | Operator |
|-----------|-------------|-------------|----------|
| Get value | `Lens.view' l s` | `view l s` | `s ^. l` |
| Set value | `Lens.set' l v s` | `set l v s` | `s & l .~ v` |
| Modify | `Lens.over' l f s` | `over l f s` | `s & l %~ f` |
| Maybe get | `Prism.preview' p s` | `preview p s` | `s ^? p` |
| Construct | `Prism.review' p v` | `review p v` | — |

### 1.3 Real-World Examples Directory

Create `examples/` with practical use cases:

- `examples/JsonLens.lean` - Navigating/modifying JSON-like structures
- `examples/ConfigUpdate.lean` - Updating nested configuration
- `examples/FormValidation.lean` - Validating form data with prisms
- `examples/TreeTraversal.lean` - Working with recursive structures
- `examples/DatabaseRecords.lean` - Updating deeply nested records

### 1.4 API Documentation Improvements

- Add `@[doc]` attributes to all public functions with examples
- Document which operations work with which optic types (capability matrix)
- Add "See also" cross-references between related functions

---

## Priority 2: Ergonomics & Developer Experience

### 2.1 Improve `makeLenses` Macro

Current limitation: Must be in a separate file from the structure definition.

**Proposed improvements:**

1. **Same-file support**: Investigate Lean 4 elaboration ordering to allow:
   ```lean
   structure Point where
     x : Float
     y : Float

   makeLenses Point  -- Works in same file
   ```

2. **Better error messages**: Instead of panicking, provide helpful errors:
   ```
   error: makeLenses: Structure 'Point' not found.
   Hint: makeLenses must be called after the structure is defined.
   If in the same file, try moving makeLenses to a later section.
   ```

3. **Selective generation**: Allow specifying which fields:
   ```lean
   makeLenses Point (only := [x])  -- Only generate x lens
   makeLenses Point (except := [_internal])  -- Skip private fields
   ```

4. **Naming control**:
   ```lean
   makeLenses Point (prefix := "point")  -- Generates pointX, pointY
   makeLenses Point (suffix := "L")      -- Generates xL, yL
   ```

### 2.2 Reduce Type Parameter Verbosity

Current pain point:
```lean
let lens := _1 (α := Nat) (β := String) (γ := Nat)
```

**Proposed solutions:**

1. **Type inference helpers**: Provide partially applied versions:
   ```lean
   def _1For (α : Type) : Lens' (α × β) α := _1
   -- Usage: _1For Nat  (infers β from context)
   ```

2. **Optic builders with better inference**:
   ```lean
   def lensOf (get : σ → α) (set : σ → α → σ) : Lens' σ α := ...
   -- More inference-friendly than current lens' constructor
   ```

3. **Documentation**: Clearly explain when type annotations are needed and patterns to avoid them.

### 2.3 Unified Import Experience

Current situation requires multiple imports:
```lean
import Collimator           -- Core types and constructors
import Collimator.Poly      -- Polymorphic operations
open Collimator.Operators   -- Operator syntax
```

**Proposed solution**: Create a "batteries included" import:
```lean
import Collimator.Prelude   -- Everything most users need

-- Equivalent to:
-- import Collimator
-- import Collimator.Poly
-- open Collimator.Operators
-- open Collimator.Instances
```

### 2.4 Better Operator Coverage

Add operators for monomorphic API users:
```lean
-- Currently only polymorphic API has operators
-- Add monomorphic variants:
scoped infixl:90 " ^.' " => Lens.view'
scoped infixr:80 " .~' " => Lens.set'
scoped infixr:80 " %~' " => Lens.over'
```

---

## Priority 3: Missing Combinators

### 3.1 Filtering Combinators

```lean
/-- Focus only on elements matching a predicate -/
def filtered (p : α → Bool) : Traversal' (List α) α

/-- Focus on elements at indices matching a predicate -/
def ifiltered (p : Nat → α → Bool) : Traversal' (List α) α

-- Usage:
over (traversed ⊚ filtered (· > 0)) (· * 2) [-1, 2, -3, 4]
-- Result: [-1, 4, -3, 8]
```

### 3.2 Safe Collection Operations

```lean
/-- Safely access head of list (returns AffineTraversal) -/
def _head : AffineTraversal' (List α) α

/-- Safely access last element -/
def _last : AffineTraversal' (List α) α

/-- Take first n elements as a traversal -/
def taking (n : Nat) : Traversal' (List α) α

/-- Drop first n elements, traverse rest -/
def dropping (n : Nat) : Traversal' (List α) α
```

### 3.3 Fold Enhancements

```lean
/-- Check if any focus matches predicate -/
def anyOf (l : Fold s a) (p : a → Bool) (s : s) : Bool

/-- Check if all foci match predicate -/
def allOf (l : Fold s a) (p : a → Bool) (s : s) : Bool

/-- Find first focus matching predicate -/
def findOf (l : Fold s a) (p : a → Bool) (s : s) : Option a

/-- Count number of foci -/
def lengthOf (l : Fold s a) (s : s) : Nat
```

### 3.4 Prism Utilities

```lean
/-- Prism that always fails (useful as identity for composition) -/
def failing : Prism' s a

/-- Combine two prisms (try first, then second) -/
def orElse (p1 p2 : Prism' s a) : AffineTraversal' s a

/-- Create prism from partial function -/
def prismFromPartial (f : s → Option a) (g : a → s) : Prism' s a
```

---

## Priority 4: Error Messages & Debugging

### 4.1 Custom Error Messages

Use Lean 4's custom error infrastructure:

```lean
-- When user tries `view` on a Prism:
macro_rules
  | `(view $p:term $s:term) =>
    if isPrism p then
      `(throwError "Cannot use 'view' on a Prism. Use 'preview' instead, which returns Option.")
    else
      `(Collimator.Poly.view $p $s)
```

### 4.2 Optic Debugging Helpers

```lean
/-- Print the structure of an optic for debugging -/
def debugOptic (name : String) (l : Lens' s a) : Lens' s a :=
  lens'
    (fun s => dbg_trace "{name}: viewing"; Lens.view' l s)
    (fun s a => dbg_trace "{name}: setting to {repr a}"; Lens.set' l a s)

/-- Trace all accesses through an optic -/
def traced (name : String) : Lens' s a → Lens' s a
```

### 4.3 Law Verification Helpers

```lean
/-- Runtime check that a lens satisfies GetPut law -/
def checkGetPut [BEq a] (l : Lens' s a) (s : s) (v : a) : Bool :=
  Lens.view' l (Lens.set' l v s) == v

/-- Test suite generator for custom optics -/
def testLensLaws (name : String) (l : Lens' s a)
    (samples : List (s × a)) : IO Unit
```

---

## Priority 5: Advanced Features

### 5.1 At/Ix Typeclass Improvements

Expand the `HasAt` and `HasIx` typeclasses:

```lean
-- Support for more container types
instance : HasAt (HashMap k v) k v
instance : HasAt (RBMap k v cmp) k v
instance : HasIx (Array α) Nat α
instance : HasIx (Vector α n) (Fin n) α
```

### 5.2 Indexed Optics Documentation & Examples

The library has indexed traversals but they're under-documented:

```lean
-- Add comprehensive examples:
example : List (Nat × String) :=
  itoListOf itraversed ["a", "b", "c"]
  -- Result: [(0, "a"), (1, "b"), (2, "c")]

-- Index-aware modifications:
example : List String :=
  iover itraversed (fun i s => s!"{i}:{s}") ["a", "b", "c"]
  -- Result: ["0:a", "1:b", "2:c"]
```

### 5.3 Bifunctor/Bitraversable Support

```lean
/-- Traverse both sides of a product -/
def both : Traversal (α × α) (β × β) α β

/-- Traverse both sides of an Either/Sum -/
def chosen : Traversal (Sum α α) (Sum β β) α β
```

### 5.4 Plated/Recursive Traversals

For recursive data structures:

```lean
/-- Typeclass for types with recursive self-similar structure -/
class Plated (α : Type) where
  plate : Traversal' α α

/-- Traverse all recursive children -/
def cosmos : [Plated α] → Fold α α

/-- Transform bottom-up -/
def transform : [Plated α] → (α → α) → α → α

/-- Transform top-down -/
def rewrite : [Plated α] → (α → Option α) → α → α
```

---

## Priority 6: Performance & Integration

### 6.1 Performance Guidelines

Document performance characteristics:

- When optic composition has overhead vs. manual code
- Guidance on when to use traversals vs. manual recursion
- Benchmarks comparing optic-based vs. direct updates

### 6.2 Integration Patterns

Document integration with common Lean 4 patterns:

```lean
-- With Except/Result for error handling
def validateWith (p : Prism' s a) (validate : a → Except e a) : s → Except e s

-- With StateM for stateful updates
def modifyThrough (l : Lens' s a) : StateM a Unit → StateM s Unit

-- With IO for effectful access
def readThrough (l : Lens' s a) : IO a → IO s
```

### 6.3 Interop with Mathlib

- Document which Mathlib structures have optic instances
- Provide bridge instances where useful
- Consider optics for mathematical structures (matrices, polynomials, etc.)

---

## Priority 7: Tooling

### 7.1 IDE Support

- LSP hover information showing optic type and supported operations
- Go-to-definition through composed optics
- Autocomplete suggestions based on available instances

### 7.2 Property-Based Testing Integration

Integrate with Plausible for automatic law checking:

```lean
-- Automatic property generation for custom optics
#check_lens_laws myLens (samples := 100)
#check_prism_laws myPrism (samples := 100)
```

### 7.3 Optic Visualization

A tool to visualize optic composition chains:

```
companyLens ⊚ departmentsTraversal ⊚ employeesTraversal ⊚ salaryLens
     │              │                      │                  │
   Lens          Traversal             Traversal            Lens
     │              │                      │                  │
Company ──────► [Department] ────────► [Employee] ────────► Salary
                (many)                  (many)            (single)

Result: Traversal Company Company Salary Salary
        (focuses on all salaries in all departments)
```

---

## Implementation Roadmap

### Phase 1: Documentation (Low effort, high impact)
- [ ] Create tutorial.md
- [ ] Create cheatsheet.md
- [ ] Add examples/ directory with 5 practical examples
- [ ] Improve inline documentation

### Phase 2: Quick Ergonomic Wins (Medium effort)
- [ ] Create Collimator.Prelude unified import
- [ ] Add monomorphic operators
- [ ] Document type annotation patterns

### Phase 3: Combinator Expansion (Medium effort)
- [ ] Implement filtered/ifiltered
- [ ] Implement _head/_last/taking/dropping
- [ ] Implement fold helpers (anyOf, allOf, findOf)
- [ ] Add Prism utilities

### Phase 4: makeLenses Improvements (Higher effort)
- [ ] Investigate same-file support
- [ ] Improve error messages
- [ ] Add configuration options

### Phase 5: Advanced Features (Higher effort)
- [ ] Expand HasAt/HasIx instances
- [ ] Document and improve indexed optics
- [ ] Consider Plated typeclass

### Phase 6: Tooling (Highest effort)
- [ ] Property-based testing integration
- [ ] IDE support improvements
- [ ] Visualization tools

---

## Feedback Welcome

If you're using Collimator and have suggestions or pain points not covered here, please open an issue or contribute directly. The goal is to make profunctor optics as pleasant to use in Lean 4 as they are in Haskell.
