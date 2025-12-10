# Collimator Cheat Sheet

Quick reference for the Collimator profunctor optics library.

## Operations Quick Reference

| Operation | Monomorphic | Polymorphic | Operator |
|-----------|-------------|-------------|----------|
| Extract | `Lens.view' l s` | `view l s` | `s ^. l` |
| Extract (optional) | `Prism.preview' p s` | `preview p s` | `s ^? p` |
| Modify | `Lens.over' l f s` | `over l f s` | `l %~ f` (then `s & ...`) |
| Set | `Lens.set' l v s` | `set l v s` | `l .~ v` (then `s & ...`) |
| Construct | `review' p v` | `review p v` | — |
| Traverse | `Traversal.traverse' tr f s` | `traverse tr f s` | — |
| Collect | `Fold.toList fld s` | — | — |

### Monomorphic Operators (with `'`)

```lean
-- Using monomorphic API directly (avoids typeclass resolution)
s ^.' l       -- view' l s
l .~' v       -- set' l v
l %~' f       -- over' l f
s ^?' p       -- preview' p s
```

## Optic Type Selection Guide

| Your data shape | Optic type | Can view? | Can modify? | Focus count |
|-----------------|------------|-----------|-------------|-------------|
| Always present field | `Lens` | ✓ Yes | ✓ Yes | Exactly 1 |
| Optional field | `Prism` | preview | ✓ Yes | 0 or 1 |
| Collection elements | `Traversal` | collect | ✓ Yes | 0 or more |
| Safe index/lookup | `AffineTraversal` | preview | ✓ Yes | 0 or 1 |
| Bidirectional conversion | `Iso` | ✓ Yes | ✓ Yes | Exactly 1 |
| Read-only access | `Fold` | collect | ✗ No | 0 or more |
| Write-only access | `Setter` | ✗ No | ✓ Yes | 0 or more |

## Composition Results

| Outer | Inner | Result |
|-------|-------|--------|
| `Lens` | `Lens` | `Lens` |
| `Lens` | `Prism` | `AffineTraversal` |
| `Lens` | `Traversal` | `Traversal` |
| `Lens` | `AffineTraversal` | `AffineTraversal` |
| `Prism` | `Prism` | `Prism` |
| `Prism` | `Lens` | `AffineTraversal` |
| `Traversal` | `Traversal` | `Traversal` |
| `Traversal` | `Lens` | `Traversal` |
| `Traversal` | `Prism` | `Traversal` |
| `Iso` | anything | preserves inner type |

## Import Cheat Sheet

```lean
-- Everything (recommended for getting started)
import Collimator.Prelude

-- Or import individually:
import Collimator                    -- All core types
import Collimator.Poly               -- Polymorphic API (view, over, set, etc.)

-- Open operators (⊚, ^., ^?, %~, .~, &)
open scoped Collimator.Operators

-- Specific instances
open Collimator.Instances.List (traversed ix)
open Collimator.Instances.Option (somePrism somePrism')
open Collimator.Instances.Sum (left left' right right')
open Collimator.Instances.Prod (_1 _2)

-- Filtering and list operations
open Collimator.Combinators (filtered filteredList _head _last taking dropping)

-- Fold utilities
open Collimator.Fold (toList anyOf allOf findOf lengthOf)

-- Auto-generate lenses (must be in separate file from structure!)
open Collimator.Derive in makeLenses MyStructure
```

## Common Constructors

```lean
-- Lens: from getter + setter
lens' (get : s → a) (set : s → a → s) : Lens' s a

-- Prism: from builder + matcher
prism (build : a → s) (split : s → Sum s a) : Prism' s a

-- Prism: from partial function (easier)
prismFromPartial (match_ : s → Option a) (build : a → s) : Prism' s a

-- Iso: from forward + backward
iso (forward : s → a) (back : a → s) : Iso' s a

-- Traversal: from polymorphic walker
traversal (walk : ∀ {F} [Applicative F], (a → F a) → s → F s) : Traversal' s a
```

## New Combinators

### Filtering

```lean
-- Focus on elements matching a predicate
filteredList (p : a → Bool) : Traversal' (List a) a
ifilteredList (p : Nat → a → Bool) : Traversal' (List a) a

-- Example: double only positive numbers
over (filteredList (· > 0)) (· * 2) [-1, 2, -3, 4]
-- Result: [-1, 4, -3, 8]
```

### Safe List Operations

```lean
-- Safely access head/last (returns AffineTraversal since list may be empty)
_head : AffineTraversal' (List a) a
_last : AffineTraversal' (List a) a

-- Traverse first n / skip first n
taking (n : Nat) : Traversal' (List a) a
dropping (n : Nat) : Traversal' (List a) a

-- Examples
preview _head [1, 2, 3]           -- some 1
preview _head []                  -- none
over (taking 2) (· * 10) [1,2,3,4] -- [10, 20, 3, 4]
```

### Fold Enhancements

```lean
-- Predicates
anyOf fld (· > 3) [1, 2, 5]      -- true
allOf fld (· > 0) [1, 2, 3]      -- true

-- Find and count
findOf fld (· > 2) [1, 2, 3, 4]  -- some 3
lengthOf fld [1, 2, 3, 4, 5]     -- 5
```

### Prism Utilities

```lean
-- Prism that always fails
failing : Prism' s a

-- Create prism from partial function
prismFromPartial (fun n => if n % 2 == 0 then some n else none) id

-- Try first prism, then second
orElse p1 p2 : AffineTraversal' s a
```

## Common Patterns

### Deep Access

```lean
-- Navigate: Company → departments → [0] → employees → [0] → salary
let salaryPath := departmentsLens ⊚ _head ⊚ employeesLens ⊚ _head ⊚ salaryLens

-- View
view salaryPath company

-- Modify
over salaryPath (· * 1.1) company  -- 10% raise
```

### Optional Data

```lean
-- Safely access nested optional field
company ^? (ceoLens ⊚ somePrism' ⊚ addressLens ⊚ cityLens)
```

### Batch Updates

```lean
-- Give all employees a raise
over (employeesTraversal ⊚ salaryLens) (· * 1.1) department

-- Update only matching employees
over (employeesTraversal ⊚ filtered (·.level > 5) ⊚ salaryLens) (· * 1.2) department
```

### Collecting Data

```lean
-- Get all employee names
Fold.toList (employeesTraversal ⊚ nameLens) department

-- Check if any employee earns > 100k
Fold.anyOf (employeesTraversal ⊚ salaryLens) (· > 100000) department
```

## Type Inference Helpers

```lean
import Collimator.Helpers

-- Instead of: _1 (α := Nat) (β := String) (γ := Nat)
first' Nat String  -- Lens' (Nat × String) Nat

-- Type-explicit builders
lensOf Point Int (·.x) (fun p x => { p with x := x })
prismOf Int Int id (fun n => if n > 0 then some n else none)

-- Type-explicit common optics
some' Int        -- Prism' (Option Int) Int
each' Int        -- Traversal' (List Int) Int
```
