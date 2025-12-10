-- Re-exports for simplified usage
import Collimator.Exports

-- Core types and optics
import Collimator.Optics.Types
import Collimator.Optics.Iso
import Collimator.Optics.Lens
import Collimator.Optics.Prism
import Collimator.Optics.Affine
import Collimator.Optics.Traversal
import Collimator.Optics.Fold
import Collimator.Optics.Setter
import Collimator.Optics.Getter
import Collimator.Optics.Review

-- Polymorphic API
import Collimator.Poly

-- Combinators and operators
import Collimator.Combinators.Composition
import Collimator.Combinators.Operators
import Collimator.Combinators.Indexed
import Collimator.Combinators.Filtered
import Collimator.Combinators.ListOps
import Collimator.Combinators.PrismOps

-- Type instances
import Collimator.Instances.Array
import Collimator.Instances.List
import Collimator.Instances.Option
import Collimator.Instances.Prod
import Collimator.Instances.Sum

-- Derive macros
import Collimator.Derive.Lenses

/-!
# Collimator Prelude

A "batteries included" import for common Collimator usage. This module imports
everything most users need and re-exports commonly used functions.

## Usage

```lean
import Collimator.Prelude

open Collimator                    -- Core types + polymorphic API
open scoped Collimator.Operators   -- Infix operators (⊚, ^., %~, .~, &)

-- You now have access to:
-- - All optic types (Lens, Prism, Iso, Traversal, etc.)
-- - Polymorphic API (view, over, set, preview, review, traverse)
-- - Fold functions (toListOf, sumOf, lengthOf, anyOf, allOf, etc.)
-- - Combinators (filtered, filteredList, composition functions)
-- - Helpers (first', second', lensOf, prismOf, some', each')
-- - Instance optics for List, Array, Option, Prod, Sum
-- - Derive macros (makeLenses)
```

## What's Included

With `open Collimator` you get:
- Core optic types and constructors
- Polymorphic API (`view`, `over`, `set`, `preview`, `review`, `traverse`)
- Fold functions (`toListOf`, `sumOf`, `lengthOf`, etc.)
- Combinators (`filtered`, `filteredList`, composition functions)
- Type inference helpers (`first'`, `second'`, `lensOf`, etc.)

With `open scoped Collimator.Operators` you get:
- `⊚` - composition
- `^.` / `^.'` - view
- `^?` / `^?'` - preview
- `%~` / `%~'` - over
- `.~` / `.~'` - set
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
