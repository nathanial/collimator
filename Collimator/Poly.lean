import Collimator.Poly.Classes
import Collimator.Poly.Instances.Lens
import Collimator.Poly.Instances.Prism
import Collimator.Poly.Instances.Traversal
import Collimator.Poly.Instances.Affine
import Collimator.Poly.Instances.Iso  -- Import Iso last so it has highest priority

/-!
# Polymorphic Optics API

This module provides a polymorphic API for working with optics, allowing
you to use the same function names (`view`, `over`, `set`, etc.) across
different optic types through type class resolution.

## Quick Start

```lean
import Collimator.Poly

open Collimator.Poly

-- Now you can use view, over, set, etc. with any compatible optic!
def example (l : Lens' s a) (i : Iso' s a) (p : Prism' s a) (x : s) : a :=
  view l x  -- Works with Lens
  view i x  -- Also works with Iso!
  -- preview p x would return Option a for Prism
```

## Type Classes

This API provides six type classes that enable polymorphic operations:

- **`HasView`** - Extract values (Iso, Lens)
  - `view : optic s a → s → a`

- **`HasOver`** - Modify focused values (Iso, Lens, Prism, AffineTraversal, Traversal)
  - `over : optic s t a b → (a → b) → s → t`

- **`HasSet`** - Set focused values (Iso, Lens, Prism, AffineTraversal, Traversal)
  - `set : optic s t a b → b → s → t`

- **`HasPreview`** - Optionally extract values (Iso, Lens, Prism, AffineTraversal)
  - `preview : optic s a → s → Option a`

- **`HasReview`** - Construct from values (Iso, Prism)
  - `review : optic s t a b → b → t`

- **`HasTraverse`** - Effectful traversal (Iso, Lens, Prism, AffineTraversal, Traversal)
  - `traverse : [Applicative F] → optic s t a b → (a → F b) → s → F t`

## Supported Optic Types

All major optic types now have complete polymorphic instances:

| Optic Type       | view | over | set | preview | review | traverse |
|------------------|------|------|-----|---------|--------|----------|
| Iso              | ✓    | ✓    | ✓   | ✓       | ✓      | ✓        |
| Lens             | ✓    | ✓    | ✓   | ✓       |        | ✓        |
| Prism            |      | ✓    | ✓   | ✓       | ✓      | ✓        |
| AffineTraversal  |      | ✓    | ✓   | ✓       |        | ✓        |
| Traversal        |      | ✓    | ✓   |         |        | ✓        |

## Usage Examples

### Basic Operations

```lean
-- Iso: bidirectional transformations
def complexIso : Iso' Complex (Float × Float) := ...
let pair := view complexIso myComplex          -- Extract as pair
let complex' := review complexIso (3.0, 4.0)   -- Construct from pair
let complex'' := over complexIso (·.1 + 1, ·.2) myComplex

-- Lens: focus on a part
def fstLens : Lens' (Int × String) Int := ...
let n := view fstLens myPair                   -- Get first element
let pair' := set fstLens 42 myPair             -- Set first element
let pair'' := over fstLens (· + 1) myPair      -- Modify first element

-- Prism: optional focus
def somePrism : Prism' (Option Int) Int := ...
let opt := preview somePrism myOption          -- Maybe extract
let opt' := review somePrism 42                -- Construct: some 42
let opt'' := over somePrism (· * 2) myOption   -- Modify if present

-- Traversal: multiple foci
def eachList : Traversal' (List Int) Int := Traversal.eachList
let list' := over eachList (· + 1) myList      -- Increment all elements
let list'' := set eachList 0 myList            -- Set all to 0
```

### Effectful Operations

```lean
-- Traverse with IO effects
def readFiles (paths : List String) : IO (List String) :=
  traverse Traversal.eachList IO.readFile paths

-- Traverse with State effects
def numberElements [Monad m] [MonadState Nat m]
    (list : List α) : m (List (Nat × α)) :=
  traverse Traversal.eachList (fun a => do
    let n ← get
    set (n + 1)
    pure (n, a)
  ) list
```

### Polymorphic Functions

Write functions that work with any optic supporting a given operation:

```lean
-- Works with any optic that supports 'over'
def increment [HasOver optic] (o : optic s t Int Int) : s → t :=
  over o (· + 1)

-- Can be used with Lens, Prism, Traversal, etc.
let pair' := increment fstLens myPair
let list' := increment eachList myList
let opt' := increment somePrism myOption
```

## Namespace Strategy

This polymorphic API lives in the `Collimator.Poly` namespace, separate
from the existing monomorphic functions in `Collimator`. This ensures:

1. **Zero breaking changes** - Existing code continues to work
2. **Clear separation** - Monomorphic vs polymorphic is explicit
3. **User choice** - You decide which namespace to open

## Migration from Monomorphic API

**Before (monomorphic)**:
```lean
open Collimator
let x := view myLens s              -- Only works with Lens
let y := isoForward myIso s         -- Different function for Iso
let z := preview myPrism s          -- Different function for Prism
```

**After (polymorphic)**:
```lean
open Collimator.Poly
let x := view myLens s              -- Works with Lens
let y := view myIso s               -- Same function works with Iso!
let z := preview myPrism s          -- Consistent API across types
```

## Implementation

This module imports:
- `Collimator.Poly.Classes` - Type class definitions
- `Collimator.Poly.Instances.Iso` - Instances for Iso
- `Collimator.Poly.Instances.Lens` - Instances for Lens
- `Collimator.Poly.Instances.Prism` - Instances for Prism
- `Collimator.Poly.Instances.Traversal` - Instances for Traversal
- `Collimator.Poly.Instances.Affine` - Instances for AffineTraversal

All polymorphic functions are exported from the `Collimator.Poly` namespace,
so users only need to:

```lean
import Collimator.Poly
open Collimator.Poly
```

-/
