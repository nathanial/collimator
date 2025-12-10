# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Build Commands

```bash
# Build the library
lake build

# Build and run all tests
lake build collimator_tests && .lake/build/bin/collimator_tests

# Build just the test library (without running)
lake build CollimatorTests
```

## Architecture

Collimator is a profunctor optics library for Lean 4. Optics (lenses, prisms, traversals, etc.) are encoded as polymorphic functions over profunctors, enabling composable data access patterns.

### Core Abstraction Layers

**1. Profunctor Foundation (`Collimator/Core/`)**
- `Profunctor`: Base typeclass - contravariant in first arg, covariant in second
- `Strong`: Profunctors that work with products (enables lenses)
- `Choice`: Profunctors that work with sums (enables prisms)
- `Wandering`: Profunctors with `wander` for traversals
- `Closed`: Profunctors that work with function types

**2. Concrete Profunctors (`Collimator/Concrete/`)**
- `Forget R`: Extracts values, ignoring second type param (for `view`)
- `Star F`: Wraps `α → F β` for applicative effects (for `traverse`)
- `Tagged`: Ignores input, provides constant output (for `review`)
- `FunArrow`: Plain functions (for `over`)

**3. Optic Types (`Collimator/Optics/Types.lean`)**

Each optic is a structure wrapping a polymorphic function constrained by profunctor capabilities:
- `Iso s t a b`: No constraints beyond `Profunctor`
- `Lens s t a b`: Requires `Strong`
- `Prism s t a b`: Requires `Choice`
- `Traversal s t a b`: Requires `Strong`, `Choice`, and `Wandering`
- `AffineTraversal`: Requires `Strong` and `Choice` (0-or-1 focus)
- `Fold`, `Setter`: Read-only and write-only variants

Monomorphic variants use prime notation: `Lens' s a = Lens s s a a`

**4. Polymorphic API (`Collimator/Poly/`)**

Type classes (`HasView`, `HasOver`, `HasPreview`, etc.) enable unified operations across optic types:
```lean
view  : optic → s → a           -- Extract focus
over  : optic → (a → b) → s → t -- Modify focus
set   : optic → b → s → t       -- Replace focus
preview : optic → s → Option a  -- Maybe extract (for prisms)
review  : optic → b → t         -- Construct from focus
traverse : optic → (a → F b) → s → F t -- Effectful traversal
```

### Key Design Pattern

Optics work by instantiating the polymorphic profunctor `P` with specific concrete profunctors:
- Use `Forget a` to implement `view` (extracts the focus)
- Use `Star F` to implement `traverse` (threads effects)
- Use `Tagged` to implement `review` (constructs values)
- Use `FunArrow` to implement `over` (modifies in place)

### Test Structure

Tests are in `CollimatorTests/` with a simple framework in `CollimatorTests/Framework.lean`:
- `TestCase`: Structure with `name` and `run : IO Unit`
- `ensure`, `ensureEq`: Assertion functions
- `runTests`: Runs a list of test cases

## Known Issues

- `Collimator/Theorems/Equivalences.lean.wip`: Needs syntax fixes for profunctor type parameter passing
- `CollimatorTests/AdvancedShowcase/MindBending.lean.wip`: Needs termination proofs for recursive Rose tree functions
