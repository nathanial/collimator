-- Re-exports for simplified usage
import Collimator.Exports

-- Core profunctor abstractions
import Collimator.Core

-- Concrete profunctor implementations
import Collimator.Concrete.Forget
import Collimator.Concrete.Star
import Collimator.Concrete.Costar
import Collimator.Concrete.FunArrow
import Collimator.Concrete.Tagged

-- Optic type definitions
import Collimator.Optics


-- Combinators and operators
import Collimator.Combinators
import Collimator.Operators

-- Type instances
import Collimator.Instances

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

-- Integration patterns
import Collimator.Integration

-- Tooling
import Collimator.Testing
import Collimator.Tracing
import Collimator.Commands


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
- `Collimator.Combinators`: Composition and operators
- `Collimator.Instances`: Standard library type instances
- `Collimator.Theorems`: Formal proofs of optic laws
- `Collimator.Derive`: Metaprogramming for automatic lens derivation
-/
