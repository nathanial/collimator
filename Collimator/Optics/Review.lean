import Collimator.Core.Profunctor
import Collimator.Core.Choice
import Collimator.Optics.Types
import Collimator.Optics.Prism
import Collimator.Concrete.Tagged

/-!
# Review Optic

A Review is a write-only optic for constructing values.
It's the dual of Getter - while Getter extracts values, Review constructs them.

Reviews are useful when you only need to build a value from a focus
without the ability to pattern match on it.

## Encoding

Unlike other optics, Reviews are best encoded directly as construction functions,
since profunctor encodings don't add meaningful structure for write-only operations.

The key operation is `review`, which constructs a target from a focus value.
-/

namespace Collimator

open Collimator.Core
open Collimator.Concrete


/--
A Review is a write-only optic for constructing values.
It's simply a constructor function wrapped in a structure.
-/
structure Review (t : Type) (b : Type) where
  build : b → t

/-- Coercion to apply a Review as a function -/
instance : CoeFun (Review t b) (fun _ => b → t) where
  coe r := r.build

/--
Construct a Review from a constructor function.
-/
def mkReview {t b : Type} (build : b → t) : Review t b :=
  ⟨build⟩

/--
Use a Review to construct a value.
-/
def Review.review {t b : Type} (r : Review t b) (x : b) : t :=
  r.build x

/--
Every Prism can be used as a Review (forgetful conversion).
Uses the Tagged profunctor to extract just the constructor.
-/
def Review.ofPrism {s t a b : Type} (p : Prism s t a b) : Review t b :=
  ⟨fun b =>
    @p.toPrism Tagged instProfunctorTagged instChoiceTagged b⟩

/--
Every Iso can be used as a Review (forgetful conversion).
Uses the Tagged profunctor to extract just the backward function.
-/
def Review.ofIso {s t a b : Type} (i : Iso s t a b) : Review t b :=
  ⟨fun b =>
    @i.toIso Tagged instProfunctorTagged b⟩

/--
Compose two Reviews.
-/
def Review.compose {t u v : Type}
    (outer : Review t u) (inner : Review u v) : Review t v :=
  ⟨fun v => outer.build (inner.build v)⟩

end Collimator
