import Collimator.Optics.Types
import Collimator.Optics.Iso
import Collimator.Optics.Lens
import Collimator.Optics.Prism
import Collimator.Optics.Traversal
import Collimator.Optics.Affine
import Collimator.Poly
import Collimator.Optics.Fold
import Collimator.Optics.Setter
import Collimator.Combinators.Composition

namespace Collimator.Operators

open Collimator
open Collimator.Setter
open Collimator.Combinators

universe u v w

/-!
## Universal Composition Operator

This section provides a unified composition operator `∘` that works across all optic types.
The operator uses typeclass resolution to automatically select the appropriate composition
function based on the types of the operands.
-/

/--
Typeclass for composable optics. Allows using a unified composition operator
across different optic types.
-/
class Composable (α : Sort*) (β : Sort*) (γ : outParam (Sort*)) where
  /-- Compose two optics. -/
  comp : α → β → γ

-- Homogeneous compositions

instance {s t a b x y : Type u} : Composable (Iso s t a b) (Iso a b x y) (Iso s t x y) where
  comp := composeIso

instance {s t a b x y : Type u} : Composable (Lens s t a b) (Lens a b x y) (Lens s t x y) where
  comp := composeLens

instance {s t a b x y : Type u} : Composable (Prism s t a b) (Prism a b x y) (Prism s t x y) where
  comp := composePrism

instance {s t a b x y : Type u} : Composable (Traversal s t a b) (Traversal a b x y) (Traversal s t x y) where
  comp := composeTraversal

-- Heterogeneous compositions

instance {s t a b x y : Type u} : Composable (Lens s t a b) (Traversal a b x y) (Traversal s t x y) where
  comp := composeLensTraversal

instance {s t a b x y : Type u} : Composable (Traversal s t a b) (Lens a b x y) (Traversal s t x y) where
  comp := composeTraversalLens

instance {s t a b x y : Type u} : Composable (Iso s t a b) (Traversal a b x y) (Traversal s t x y) where
  comp := composeIsoTraversal

instance {s t a b x y : Type u} : Composable (Lens s t a b) (Prism a b x y) (AffineTraversal s t x y) where
  comp := composeLensPrism

instance {s t a b x y : Type u} : Composable (Traversal s t a b) (Prism a b x y) (Traversal s t x y) where
  comp := composeTraversalPrism

instance {s t a b x y : Type u} : Composable (Traversal s t a b) (AffineTraversal a b x y) (Traversal s t x y) where
  comp := composeTraversalAffine

instance {s t a b x y : Type u} : Composable (Lens s t a b) (AffineTraversal a b x y) (AffineTraversal s t x y) where
  comp := composeLensAffine

instance {s t a b x y : Type u} : Composable (AffineTraversal s t a b) (Lens a b x y) (AffineTraversal s t x y) where
  comp := composeAffineLens

instance {s t a b x y : Type u} : Composable (AffineTraversal s t a b) (AffineTraversal a b x y) (AffineTraversal s t x y) where
  comp := composeAffine

instance {s t a b x y : Type u} : Composable (AffineTraversal s t a b) (Prism a b x y) (AffineTraversal s t x y) where
  comp := composeAffinePrism

instance {s t a b x y : Type u} : Composable (Prism s t a b) (AffineTraversal a b x y) (AffineTraversal s t x y) where
  comp := composePrismAffine

-- Fold compositions

instance {s t a b x y : Type u} : Composable (Lens s t a b) (Fold a b x y) (Fold s t x y) where
  comp := Fold.composeLensFold

instance {s t a b x y : Type u} : Composable (Fold s t a b) (Fold a b x y) (Fold s t x y) where
  comp := Fold.composeFold

/--
Universal composition operator for optics. Uses typeclass resolution to select
the appropriate composition function based on the types of the operands.

Examples:
- `lens1 ⊚ lens2` resolves to `composeLens`
- `lens ⊚ traversal` resolves to `composeLensTraversal`
- `traversal ⊚ prism` resolves to `composeTraversalPrism`
-/
scoped infixr:80 " ⊚ " => Composable.comp

/-!
## Other Operators

### Operator Quick Reference

| Operator | Name | Usage | Description |
|----------|------|-------|-------------|
| `^.` | view | `s ^. lens` | Extract the focused value |
| `^?` | preview | `s ^? prism` | Extract if present (returns `Option`) |
| `%~` | over | `lens %~ f` | Modify with a function (use with `&`) |
| `.~` | set | `lens .~ v` | Replace with a value (use with `&`) |
| `&` | pipe | `s & lens .~ v` | Reverse application for chaining |
| `⊚` | compose | `lens1 ⊚ lens2` | Compose two optics |

### Examples

```lean
open scoped Collimator.Operators

structure Point where x : Int; y : Int
def xLens : Lens' Point Int := lens' (·.x) (fun p x => { p with x := x })
def yLens : Lens' Point Int := lens' (·.y) (fun p y => { p with y := y })

let p := Point.mk 10 20

-- View
p ^. xLens                    -- 10

-- Set (note: use & to apply the setter)
p & xLens .~ 99               -- { x := 99, y := 20 }

-- Modify
p & xLens %~ (· * 2)          -- { x := 20, y := 20 }

-- Chain multiple updates
p & xLens .~ 100 & yLens %~ (· + 5)  -- { x := 100, y := 25 }

-- Preview (for prisms/optional access)
(some 42) ^? somePrism'       -- some 42
none ^? somePrism'            -- none
```
-/

/--
Reverse function application, useful for chaining optic operators.

```lean
-- Instead of: set xLens 10 (set yLens 20 point)
-- Write:      point & xLens .~ 10 & yLens .~ 20
```
-/
scoped infixl:10 " & " => fun x f => f x

/--
View through a lens using infix notation.

Extracts the focused value from the source. Works with any optic that
supports viewing (Iso, Lens, Getter).

```lean
let point := Point.mk 10 20
point ^. xLens  -- 10

-- Composed access
let nested := { outer := { inner := 42 } }
nested ^. outerLens ⊚ innerLens  -- 42
```
-/
scoped infixl:60 " ^. " => fun s l => Collimator.Poly.view l s

/--
Preview through a prism using infix notation.

Attempts to extract the focused value, returning `Option`. Returns `some`
if the prism matches, `none` otherwise. Works with Prism, AffineTraversal.

```lean
(some 42) ^? somePrism'    -- some 42
none ^? somePrism'         -- none

-- Safe head access
[1, 2, 3] ^? _head         -- some 1
[] ^? _head                -- none
```
-/
scoped infixl:60 " ^? " => fun s p => Collimator.Poly.preview p s

/--
Modify the focus of a setter-like optic.

Returns a function `s → t` that modifies the focused part(s). Use with `&`
for a fluent syntax.

```lean
-- Modify single field
point & xLens %~ (· + 1)           -- increment x

-- Modify all elements in a traversal
[1, 2, 3] & traversed %~ (· * 2)   -- [2, 4, 6]

-- Chained modifications
point & xLens %~ (· * 2) & yLens %~ (· + 10)
```
-/
scoped infixr:80 "%~" => fun optic f => Collimator.Poly.over optic f

/--
Set the focus of a setter-like optic to a constant value.

Returns a function `s → t` that replaces the focused part(s). Use with `&`
for a fluent syntax.

```lean
-- Set single field
point & xLens .~ 100               -- { x := 100, y := 20 }

-- Set all elements in a traversal
[1, 2, 3] & traversed .~ 0         -- [0, 0, 0]

-- Chained sets
point & xLens .~ 10 & yLens .~ 20  -- { x := 10, y := 20 }
```
-/
scoped infixr:80 ".~" => fun optic value => Collimator.Poly.set optic value

/-!
## Monomorphic Operators

These operators work directly with the monomorphic API functions (`view'`, `over'`, etc.),
avoiding type class resolution overhead for simple cases where you're working with
monomorphic optics like `Lens'` or `Prism'`.
-/

/-- View through a lens using monomorphic API. Avoids typeclass resolution. -/
scoped infixl:60 " ^.' " => fun s l => Collimator.view' l s

/-- Set through a lens using monomorphic API. Avoids typeclass resolution. -/
scoped notation:80 l " .~' " v => Collimator.set' l v

/-- Modify through a lens using monomorphic API. Avoids typeclass resolution. -/
scoped notation:80 l " %~' " f => Collimator.over' l f

/-- Preview through a prism using monomorphic API. Avoids typeclass resolution. -/
scoped infixl:60 " ^?' " => fun s p => Collimator.preview' p s

end Collimator.Operators
