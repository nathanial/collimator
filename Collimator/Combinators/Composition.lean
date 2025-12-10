import Collimator.Optics.Types
import Collimator.Optics.Iso
import Collimator.Optics.Lens
import Collimator.Optics.Prism
import Collimator.Optics.Traversal
import Collimator.Optics.Affine

namespace Collimator.Combinators

open Collimator
open Collimator.Core

universe u

/--
Compose two isomorphisms.
-/
@[inline] def composeIso
    {s t a b u v : Type u} (outer : Iso s t a b) (inner : Iso a b u v) :
    Iso s t u v :=
  fun {P} [Profunctor P] =>
    outer.toIso (P := P) ∘ inner.toIso (P := P)

/--
Compose two lenses to focus through nested product-like structures.
-/
@[inline] def composeLens
    {s t a b u v : Type u}
    (outer : Lens s t a b) (inner : Lens a b u v) : Lens s t u v :=
  fun {P} [Profunctor P] hStrong =>
    fun puv => outer.toLens (P := P) hStrong (inner.toLens (P := P) hStrong puv)

/--
Compose two prisms to focus through nested sum-like structures.
-/
@[inline] def composePrism
    {s t a b u v : Type u}
    (outer : Prism s t a b) (inner : Prism a b u v) : Prism s t u v :=
  fun {P} [Profunctor P] hChoice =>
    fun puv => outer.toPrism (P := P) hChoice (inner.toPrism (P := P) hChoice puv)

/--
Compose a lens with a traversal. The resulting traversal iterates the inner
focus for every focus selected by the outer lens.
-/
@[inline] def composeLensTraversal
    {s t a b u v : Type u}
    (outer : Lens s t a b) (inner : Traversal a b u v) :
    Traversal s t u v :=
  fun {P} [Profunctor P] [Strong P] [Choice P] w =>
    fun puv => outer.toLens (P := P) (inferInstance : Strong P)
      (inner.toTraversal (P := P) w puv)

/--
Compose a traversal with a lens. The resulting traversal focuses the inner
lens for every element selected by the outer traversal.
-/
@[inline] def composeTraversalLens
    {s t a b u v : Type u}
    (outer : Traversal s t a b) (inner : Lens a b u v) :
    Traversal s t u v :=
  fun {P} [Profunctor P] [Strong P] [Choice P] w =>
    fun puv => outer.toTraversal (P := P) w (inner.toLens (P := P) (inferInstance : Strong P) puv)

/--
Compose two traversals, applying the inner traversal to every focus yielded by
the outer traversal.
-/
@[inline] def composeTraversal
    {s t a b u v : Type u}
    (outer : Traversal s t a b) (inner : Traversal a b u v) :
    Traversal s t u v :=
  fun {P} [Profunctor P] [Strong P] [Choice P] w =>
    fun puv => outer.toTraversal (P := P) w (inner.toTraversal (P := P) w puv)

/--
Compose an isomorphism with a traversal. The iso transforms the type, then the
traversal focuses multiple elements.
-/
@[inline] def composeIsoTraversal
    {s t a b u v : Type u}
    (outer : Iso s t a b) (inner : Traversal a b u v) :
    Traversal s t u v :=
  fun {P} [Profunctor P] [Strong P] [Choice P] w =>
    fun puv => outer.toIso (P := P) (inner.toTraversal (P := P) w puv)

/--
Compose a lens with a prism. The lens focuses exactly one element, then the
prism optionally matches a pattern within that element.
-/
@[inline] def composeLensPrism
    {s t a b u v : Type u}
    (outer : Lens s t a b) (inner : Prism a b u v) :
    AffineTraversal s t u v :=
  fun {P} [Profunctor P] [Strong P] [Choice P] =>
    fun puv => outer.toLens (P := P) (inferInstance : Strong P)
      (inner.toPrism (P := P) (inferInstance : Choice P) puv)

/--
Compose a traversal with a prism. The traversal focuses many elements, then the
prism filters by pattern matching.
-/
@[inline] def composeTraversalPrism
    {s t a b u v : Type u}
    (outer : Traversal s t a b) (inner : Prism a b u v) :
    Traversal s t u v :=
  fun {P} [Profunctor P] [Strong P] [Choice P] w =>
    fun puv => outer.toTraversal (P := P) w (inner.toPrism (P := P) (inferInstance : Choice P) puv)

/--
Compose a traversal with an affine traversal. The traversal focuses many elements,
then the affine focuses at most one element within each.
-/
@[inline] def composeTraversalAffine
    {s t a b u v : Type u}
    (outer : Traversal s t a b) (inner : AffineTraversal a b u v) :
    Traversal s t u v :=
  fun {P} [Profunctor P] [Strong P] [Choice P] w =>
    fun puv => outer.toTraversal (P := P) w
      (inner.toAffineTraversal (P := P) (inferInstance : Strong P) (inferInstance : Choice P) puv)

/--
Compose a lens with an affine traversal. The lens focuses exactly one element,
then the affine focuses at most one element within that.
-/
@[inline] def composeLensAffine
    {s t a b u v : Type u}
    (outer : Lens s t a b) (inner : AffineTraversal a b u v) :
    AffineTraversal s t u v :=
  fun {P} [Profunctor P] [Strong P] [Choice P] =>
    fun puv => outer.toLens (P := P) (inferInstance : Strong P)
      (inner.toAffineTraversal (P := P) (inferInstance : Strong P) (inferInstance : Choice P) puv)

/--
Compose an affine traversal with a lens. The affine focuses at most one element,
then the lens focuses exactly one element within that.
-/
@[inline] def composeAffineLens
    {s t a b u v : Type u}
    (outer : AffineTraversal s t a b) (inner : Lens a b u v) :
    AffineTraversal s t u v :=
  fun {P} [Profunctor P] [Strong P] [Choice P] =>
    fun puv => outer.toAffineTraversal (P := P) (inferInstance : Strong P) (inferInstance : Choice P)
      (inner.toLens (P := P) (inferInstance : Strong P) puv)

/--
Compose two affine traversals. Each focuses at most one element,
so the composition also focuses at most one element.
-/
@[inline] def composeAffine
    {s t a b u v : Type u}
    (outer : AffineTraversal s t a b) (inner : AffineTraversal a b u v) :
    AffineTraversal s t u v :=
  fun {P} [Profunctor P] [Strong P] [Choice P] =>
    fun puv => outer.toAffineTraversal (P := P) (inferInstance : Strong P) (inferInstance : Choice P)
      (inner.toAffineTraversal (P := P) (inferInstance : Strong P) (inferInstance : Choice P) puv)

/--
Compose an affine traversal with a prism. The affine focuses at most one element,
then the prism optionally matches a pattern within that.
-/
@[inline] def composeAffinePrism
    {s t a b u v : Type u}
    (outer : AffineTraversal s t a b) (inner : Prism a b u v) :
    AffineTraversal s t u v :=
  fun {P} [Profunctor P] [Strong P] [Choice P] =>
    fun puv => outer.toAffineTraversal (P := P) (inferInstance : Strong P) (inferInstance : Choice P)
      (inner.toPrism (P := P) (inferInstance : Choice P) puv)

/--
Compose a prism with an affine traversal. The prism optionally matches,
then the affine focuses at most one element within that.
-/
@[inline] def composePrismAffine
    {s t a b u v : Type u}
    (outer : Prism s t a b) (inner : AffineTraversal a b u v) :
    AffineTraversal s t u v :=
  fun {P} [Profunctor P] [Strong P] [Choice P] =>
    fun puv => outer.toPrism (P := P) (inferInstance : Choice P)
      (inner.toAffineTraversal (P := P) (inferInstance : Strong P) (inferInstance : Choice P) puv)

end Collimator.Combinators
