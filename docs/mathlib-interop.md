# Mathlib Interoperability

This guide covers how Collimator optics can work alongside Mathlib structures and concepts.

## Current Status

Collimator is designed as a standalone optics library with no Mathlib dependency. This keeps it lightweight for general use. However, optics patterns can be applied to Mathlib structures.

## Using Optics with Mathlib Types

### Vectors (Mathlib's `Fin n → α`)

```lean
import Collimator.Prelude
import Mathlib.Data.Fin.Basic

-- Lens to access element at index
def vecAt (i : Fin n) : Lens' (Fin n → α) α :=
  lens'
    (fun v => v i)
    (fun v a j => if i = j then a else v j)

-- Usage
def myVec : Fin 3 → Int := ![1, 2, 3]
let updated := set' (vecAt 1) 99 myVec  -- ![1, 99, 3]
```

### Matrices

```lean
import Mathlib.Data.Matrix.Basic

-- Lens for matrix entry at (i, j)
def matrixAt (i : Fin m) (j : Fin n) : Lens' (Matrix (Fin m) (Fin n) α) α :=
  lens'
    (fun M => M i j)
    (fun M a => M.updateRow i (M i).update j a)

-- Traversal over all entries
def matrixEntries : Traversal' (Matrix (Fin m) (Fin n) α) α :=
  traversal fun {F} [Applicative F] f M =>
    -- Traverse row by row
    Matrix.of fun i j => f (M i j)  -- Simplified; actual impl needs sequencing
```

### Polynomials

```lean
import Mathlib.Algebra.Polynomial.Basic

-- Lens for the leading coefficient
def leadingCoeff [Semiring R] [DecidableEq R] : Lens' (Polynomial R) R :=
  lens'
    (fun p => p.leadingCoeff)
    (fun p c => p - C p.leadingCoeff * X^p.natDegree + C c * X^p.natDegree)

-- Access coefficient at degree n
def coeffAt [Semiring R] (n : Nat) : Lens' (Polynomial R) R :=
  lens'
    (fun p => p.coeff n)
    (fun p c => p + C (c - p.coeff n) * X^n)
```

## Bridge Instances

If your project uses both Collimator and Mathlib, you can create bridge instances:

### HasAt for Mathlib Vectors

```lean
import Collimator.Combinators.Indexed
import Mathlib.Data.Fin.VecNotation

-- Make Fin-indexed functions work with HasAt
instance : HasAt (Fin n) (Fin n → α) α where
  focus i := lens' (· i) (fun v a j => if i = j then a else v j)

-- Now you can use atLens with vectors
let v := ![10, 20, 30]
let elem := view' (atLens 1) v  -- some 20
```

### HasIx for Mathlib Types

```lean
instance : HasIx (Fin n) (Fin n → α) α where
  ix i := traversal fun {F} [Applicative F] f v =>
    pure (fun a j => if i = j then a else v j) <*> f (v i)
```

## Conceptual Connections

### Optics and Category Theory

Profunctor optics have deep connections to category theory that Mathlib users might appreciate:

| Optic | Category Theory Connection |
|-------|---------------------------|
| Iso | Isomorphism in a category |
| Lens | Coalgebra for the store comonad |
| Prism | Algebra for the error monad |
| Traversal | Natural transformation from applicative |

### Lawfulness

Collimator includes formal proofs of optic laws in `Collimator/Theorems/`:
- `IsoLaws.lean` - Round-trip laws
- `LensLaws.lean` - GetPut, PutGet, PutPut
- `PrismLaws.lean` - Preview-Review laws
- `TraversalLaws.lean` - Identity and composition laws

These proofs are self-contained but follow patterns familiar to Mathlib users.

## Writing Custom Instances

When working with Mathlib types, follow these patterns:

### For Product-like Types (use Lens)

```lean
-- If your type has a projection and reconstruction
def myLens : Lens' MyType Part :=
  lens' getPart setPart
```

### For Sum-like Types (use Prism)

```lean
-- If your type has constructors and pattern matching
def myPrism : Prism' MyType Constructor :=
  prismFromPartial
    (fun x => match x with | Constructor a => some a | _ => none)
    Constructor
```

### For Container-like Types (use Traversal)

```lean
-- If your type contains multiple elements
def myTraversal : Traversal' Container Element :=
  traversal fun {F} [Applicative F] f container =>
    -- Traverse each element applicatively
```

## Performance Considerations

When using optics with Mathlib's computational structures:

1. **Evaluation**: Mathlib often uses definitions that don't compute well. Optics inherit this.
2. **Decidability**: Some optics require decidable equality; ensure your Mathlib types provide it.
3. **Universe levels**: Collimator uses `Type u`; match with Mathlib's universe requirements.

## Future Directions

Potential areas for deeper integration:

1. **Optic morphisms**: Connect optic composition with Mathlib's category morphisms
2. **Lawfulness proofs**: Use Mathlib's tactic library for more automated proofs
3. **Algebraic structures**: Optics for monoids, groups, rings, etc.
4. **Type class hierarchy**: Bridge Collimator's profunctor hierarchy with Mathlib's

## Contributing

If you develop useful Mathlib bridges, consider:
1. Creating a separate `collimator-mathlib` package
2. Contributing examples to the Collimator repository
3. Documenting patterns that work well

The goal is to keep Collimator's core dependency-free while enabling rich interoperability.
