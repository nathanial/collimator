-- Re-exports for simplified usage
import Collimator.Exports

-- Core types and optics
import Collimator.Optics

-- Combinators and operators
import Collimator.Combinators
import Collimator.Operators

-- Type instances
import Collimator.Instances

-- Derive macros
import Collimator.Derive.Lenses

/-!
# Collimator Prelude

A "batteries included" import for common Collimator usage. This module imports
everything most users need and re-exports commonly used functions.

## Usage

```lean
import Collimator.Prelude

open Collimator                    -- Core types and optics
open scoped Collimator.Operators   -- Infix operators (^., ^?, %~, .~, &)

-- You now have access to:
-- - All optic types (Lens, Prism, Iso, Traversal, etc.)
-- - Monomorphic API (view', over', set', preview', review')
-- - Fold functions (toListOf, sumOf, lengthOf, anyOf, allOf, etc.)
-- - Combinators (filtered, filteredList, composition functions)
-- - Helpers (first', second', lensOf, prismOf, some', each')
-- - Instance optics for List, Array, Option, Prod, Sum
-- - Derive macros (makeLenses)
```

## What's Included

With `open Collimator` you get:
- Core optic types and constructors
- Monomorphic API (`view'`, `over'`, `set'`, `preview'`, `review'`)
- Fold functions (`toListOf`, `sumOf`, `lengthOf`, etc.)
- Combinators (`filtered`, `filteredList`, composition functions)
- Type inference helpers (`first'`, `second'`, `lensOf`, etc.)

With `open scoped Collimator.Operators` you get:
- `^.` - view
- `^?` - preview
- `%~` - over
- `.~` - set
- `&` - reverse application

## Advanced Namespaces (opt-in)

For advanced use cases, these namespaces require explicit opening:
- `Collimator.Core` - Low-level profunctor abstractions
- `Collimator.Instances.*` - Per-type instance optics (traversed, somePrism', etc.)
- `Collimator.Theorems` - Proofs of optic laws
- `Collimator.Debug` - Debugging utilities
-/

-- Open operators with scoped so they're available but don't pollute global namespace
open scoped Collimator.Operators
