/-!
# Collimator: Profunctor Optics for Lean 4

A comprehensive optics library based on profunctor encodings.

## Quick Start

```lean
import Collimator.Prelude

open Collimator
open scoped Collimator.Operators

-- Define a lens
def xLens : Lens' Point Int := lens' (·.x) (fun p x => { p with x := x })

-- Use it
#eval point ^. xLens              -- view
#eval point & xLens .~ 10         -- set
#eval point & xLens %~ (· + 1)    -- over
```

## Main modules

- `Collimator.Core`: Profunctor abstractions (Profunctor, Strong, Choice, Wandering, Closed)
- `Collimator.Concrete`: Concrete profunctor implementations (Forget, Star, Costar, FunArrow, Tagged)
- `Collimator.Optics`: Optic type definitions (Iso, Lens, Prism, Affine, Traversal, Fold, Setter)
- `Collimator.Poly`: Polymorphic API with type classes
- `Collimator.Combinators`: Composition and operators
- `Collimator.Instances`: Standard library type instances
- `Collimator.Theorems`: Formal proofs of optic laws
- `Collimator.Derive`: Metaprogramming for automatic lens derivation
-/

-- Re-exports for simplified usage
import Collimator.Exports

-- Core profunctor abstractions
import Collimator.Core.Profunctor
import Collimator.Core.Strong
import Collimator.Core.StrongLaws
import Collimator.Core.Choice
import Collimator.Core.ChoiceLaws
import Collimator.Core.Closed
import Collimator.Core.Wandering
import Collimator.Core.Laws

-- Concrete profunctor implementations
import Collimator.Concrete.Forget
import Collimator.Concrete.Star
import Collimator.Concrete.Costar
import Collimator.Concrete.FunArrow
import Collimator.Concrete.Tagged

-- Optic type definitions
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
import Collimator.Combinators.Bitraversal
import Collimator.Combinators.Plated

-- Type instances
import Collimator.Instances.Array
import Collimator.Instances.List
import Collimator.Instances.Option
import Collimator.Instances.Prod
import Collimator.Instances.Sum
import Collimator.Instances.String

-- Theorems and proofs
import Collimator.Theorems.IsoLaws
import Collimator.Theorems.LensLaws
import Collimator.Theorems.PrismLaws
import Collimator.Theorems.AffineLaws
import Collimator.Theorems.TraversalLaws
import Collimator.Theorems.Equivalences
import Collimator.Theorems.Subtyping
import Collimator.Theorems.Normalization
import Collimator.Theorems.TraversalFusion

-- Derive macros
import Collimator.Derive.Lenses

-- Helpers for type inference
import Collimator.Helpers

-- Debug utilities
import Collimator.Debug
import Collimator.Debug.LawCheck
import Collimator.Poly.Guidance

-- Integration patterns
import Collimator.Integration

-- Tooling
import Collimator.Testing
import Collimator.Tracing
import Collimator.Commands
