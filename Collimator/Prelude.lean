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
everything most users need and opens the commonly used namespaces.

## Usage

```lean
import Collimator.Prelude

-- You now have access to:
-- - All optic types (Lens, Prism, Iso, Traversal, etc.)
-- - Polymorphic API (view, over, set, preview, review, traverse)
-- - Operators (⊚, ^., ^?, %~, .~, &)
-- - Instance optics for List, Array, Option, Prod, Sum
-- - Derive macros (makeLenses)
```

## What's Included

- `Collimator` - Core types and constructors
- `Collimator.Poly` - Polymorphic API
- `Collimator.Operators` - Infix operators (scoped)
- All instance modules (List, Array, Option, Prod, Sum)
- Derive macros

## Alternative: Selective Imports

If you prefer more control, import modules individually:
```lean
import Collimator                 -- Just core types
import Collimator.Poly            -- Add polymorphic API
import Collimator.Instances.List  -- Add specific instances
```
-/

-- Open operators with scoped so they're available but don't pollute global namespace
open scoped Collimator.Operators
