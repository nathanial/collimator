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
-/

/-- Reverse function application, useful for chaining optic operators. -/
scoped infixl:10 " & " => fun x f => f x

/-- View through a lens using infix notation. -/
scoped infixl:60 " ^. " => fun s l => Collimator.Poly.view l s

/-- Preview through a prism using infix notation. -/
scoped infixl:60 " ^? " => fun s p => Collimator.Poly.preview p s

/-- Modify the focus of a setter-like optic. -/
scoped infixr:80 "%~" => fun optic f => Collimator.Poly.over optic f

/-- Set the focus of a setter-like optic to a constant value. -/
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
