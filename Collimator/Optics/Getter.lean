import Collimator.Core.Profunctor
import Collimator.Core.Strong
import Collimator.Optics.Types
import Collimator.Optics.Lens
import Collimator.Concrete.Forget

/-!
# Getter Optic

A Getter is a read-only optic that focuses on exactly one value.
It's simpler than a Lens because it doesn't require a setter.

Getters are useful when you only need to extract data from a structure
without the ability to modify it.

## Encoding

Unlike other optics, Getters are best encoded directly as getter functions,
since profunctor encodings don't add meaningful structure for read-only operations.

The key operation is `view`, which extracts the focus from the source.
-/

namespace Collimator

open Collimator.Core
open Collimator.Concrete


/--
A Getter is a read-only optic for exactly one focus.
It's simply a getter function wrapped in a structure.
-/
structure Getter (s : Type) (a : Type) : Type 1 where
  get : s → a

/-- Coercion to apply a Getter as a function -/
instance : CoeFun (Getter s a) (fun _ => s → a) where
  coe g := g.get

/--
Construct a Getter from a getter function.
-/
def getter {s a : Type} (get : s → a) : Getter s a :=
  ⟨get⟩

/-- Alias for `getter` -/
abbrev getter' {s a : Type} := @getter s a

/--
View the focus of a Getter.
-/
def Getter.view {s a : Type} (g : Getter s a) (x : s) : a :=
  g.get x

/--
Every Lens can be used as a Getter (forgetful conversion).
Uses the Forget profunctor to extract just the getter.
-/
def Getter.ofLens {s t a b : Type} (l : Lens s t a b) : Getter s a :=
  ⟨fun s =>
    let forget : Forget a a a := fun a => a
    (l (P := Forget a) forget) s⟩

/--
Compose two Getters.
-/
def Getter.compose {s a b : Type}
    (outer : Getter s a) (inner : Getter a b) : Getter s b :=
  ⟨fun s => inner.get (outer.get s)⟩

end Collimator
