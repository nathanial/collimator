import Collimator.Core
import Batteries
import Collimator.Concrete.Forget
import Collimator.Concrete.FunArrow
import Collimator.Concrete.Tagged
import Collimator.Concrete.Star

namespace Collimator

open Batteries
open Collimator.Core
open Collimator.Concrete

/-!
# Optic Types

Optics are defined as type aliases for polymorphic functions over profunctors.
This encoding allows standard function composition (`∘`) to work naturally:

```lean
lens1 ∘ lens2  -- composes two lenses
lens ∘ prism   -- composes a lens with a prism (gives AffineTraversal)
```

The profunctor constraints determine what operations each optic supports:
- `Profunctor P` alone: Iso (bidirectional transformation)
- `Strong P`: Lens (product-like access)
- `Choice P`: Prism (sum-like access)
- `Strong P + Choice P`: AffineTraversal (0-or-1 focus)
- `Strong P + Choice P + Wandering P`: Traversal (0-to-many focus)
-/

/--
`Optic C s t a b` quantifies over all profunctors satisfying the constraint `C`.
-/
def Optic (C : (Type → Type → Type) → Prop)
    (s t a b : Type) : Type 1 :=
  ∀ {P : Type → Type → Type} [Profunctor P], C P → P a b → P s t

/--
Isomorphisms are optics constrained only by the profunctor structure.
An iso witnesses that `s` and `a` are isomorphic (and `t` and `b`).
-/
def Iso (s t a b : Type) : Type 1 :=
  ∀ {P : Type → Type → Type} [Profunctor P], P a b → P s t

/--
Lenses require a `Strong` profunctor.
A lens focuses on exactly one `a` inside an `s`.
-/
def Lens (s t a b : Type) : Type 1 :=
  ∀ {P : Type → Type → Type} [Profunctor P] [Strong P], P a b → P s t

/--
Prisms require a `Choice` profunctor.
A prism focuses on an `a` that may or may not be present in `s`.
-/
def Prism (s t a b : Type) : Type 1 :=
  ∀ {P : Type → Type → Type} [Profunctor P] [Choice P], P a b → P s t

/--
Affine traversals require both `Strong` and `Choice`.
An affine traversal focuses on at most one `a` inside an `s`.
-/
def AffineTraversal (s t a b : Type) : Type 1 :=
  ∀ {P : Type → Type → Type} [Profunctor P] [Strong P] [Choice P], P a b → P s t

/--
Traversals require `Strong`, `Choice`, and `Wandering` profunctors.
A traversal focuses on zero or more `a` values inside an `s`.
-/
def Traversal (s t a b : Type) : Type 1 :=
  ∀ {P : Type → Type → Type} [Profunctor P] [Strong P] [Choice P] [Wandering P], P a b → P s t

/--
Folds are read-only optics that require `Strong` and `Choice`.
A fold extracts zero or more `a` values from an `s`.
-/
def Fold (s t a b : Type) : Type 1 :=
  ∀ {P : Type → Type → Type} [Profunctor P] [Strong P] [Choice P], P a b → P s t

/--
Setters are write-only optics that require `Strong`.
A setter modifies zero or more `a` values inside an `s`.
-/
def Setter (s t a b : Type) : Type 1 :=
  ∀ {P : Type → Type → Type} [Profunctor P] [Strong P], P a b → P s t

/-- Monomorphic iso (source and target types are the same). -/
abbrev Iso' (s a : Type) := Iso s s a a

/-- Monomorphic lens (source and target types are the same). -/
abbrev Lens' (s a : Type) := Lens s s a a

/-- Monomorphic prism (source and target types are the same). -/
abbrev Prism' (s a : Type) := Prism s s a a

/-- Monomorphic affine traversal (source and target types are the same). -/
abbrev AffineTraversal' (s a : Type) := AffineTraversal s s a a

/-- Monomorphic traversal (source and target types are the same). -/
abbrev Traversal' (s a : Type) := Traversal s s a a

/-- Monomorphic fold (source and target types are the same). -/
abbrev Fold' (s a : Type) := Fold s s a a

/-- Monomorphic setter (source and target types are the same). -/
abbrev Setter' (s a : Type) := Setter s s a a

/-!
## Optic Hierarchy

The optic types form a subtyping hierarchy based on their profunctor constraints:

```
        Iso
       /   \
    Lens   Prism
       \   /
   AffineTraversal ──→ Fold
         |
     Traversal ──→ Setter
```

With type aliases, this hierarchy is enforced by Lean's type system automatically.
When you compose optics with `∘`, the result type has the union of all constraints:

- `Lens ∘ Lens` = `Lens` (both need Strong)
- `Lens ∘ Prism` = `AffineTraversal` (needs Strong + Choice)
- `Lens ∘ Traversal` = `Traversal` (needs Strong + Choice + Wandering)

No explicit coercion instances are needed!
-/

/-!
## Coercion Functions

While standard function composition handles most cases automatically,
these explicit coercion functions are provided for cases where you need
to explicitly widen an optic's type.
-/

/-- Widen an Iso to a Lens. -/
@[inline] def Iso.toLens {s t a b : Type} (i : Iso s t a b) : Lens s t a b :=
  fun {P} [Profunctor P] [Strong P] => i

/-- Widen an Iso to a Prism. -/
@[inline] def Iso.toPrism {s t a b : Type} (i : Iso s t a b) : Prism s t a b :=
  fun {P} [Profunctor P] [Choice P] => i

/-- Widen an Iso to an AffineTraversal. -/
@[inline] def Iso.toAffine {s t a b : Type} (i : Iso s t a b) : AffineTraversal s t a b :=
  fun {P} [Profunctor P] [Strong P] [Choice P] => i

/-- Widen an Iso to a Traversal. -/
@[inline] def Iso.toTraversal {s t a b : Type} (i : Iso s t a b) : Traversal s t a b :=
  fun {P} [Profunctor P] [Strong P] [Choice P] [Wandering P] => i

/-- Widen a Lens to an AffineTraversal. -/
@[inline] def Lens.toAffine {s t a b : Type} (l : Lens s t a b) : AffineTraversal s t a b :=
  fun {P} [Profunctor P] [Strong P] [Choice P] => l

/-- Widen a Lens to a Traversal. -/
@[inline] def Lens.toTraversal {s t a b : Type} (l : Lens s t a b) : Traversal s t a b :=
  fun {P} [Profunctor P] [Strong P] [Choice P] [Wandering P] => l

/-- Widen a Prism to an AffineTraversal. -/
@[inline] def Prism.toAffine {s t a b : Type} (p : Prism s t a b) : AffineTraversal s t a b :=
  fun {P} [Profunctor P] [Strong P] [Choice P] => p

/-- Widen a Prism to a Traversal. -/
@[inline] def Prism.toTraversal {s t a b : Type} (p : Prism s t a b) : Traversal s t a b :=
  fun {P} [Profunctor P] [Strong P] [Choice P] [Wandering P] => p

/-- Widen an AffineTraversal to a Traversal. -/
@[inline] def AffineTraversal.toTraversal {s t a b : Type} (aff : AffineTraversal s t a b) : Traversal s t a b :=
  fun {P} [Profunctor P] [Strong P] [Choice P] [Wandering P] => aff

/-!
## Iso Construction and Operations
-/

/--
Create an isomorphism from forward and backward maps.

An isomorphism represents a bidirectional, lossless transformation between
two types. Every iso can be used as a lens (viewing/modifying) or a prism
(constructing/pattern-matching).

## Parameters
- `forward`: Transform from source type to focus type
- `back`: Transform from focus type back to source type

## Example

```lean
-- Isomorphism between Bool and Nat (0/1)
def boolNat : Iso' Bool Nat :=
  iso
    (forward := fun b => if b then 1 else 0)
    (back := fun n => n != 0)

-- String ↔ List Char
def stringChars : Iso' String (List Char) :=
  iso (forward := String.toList) (back := String.mk)

-- Usage with lens operations:
view boolNat true           -- 1
over boolNat (· + 10) false -- true (because 10 != 0)

-- Usage with prism operations:
review boolNat 42           -- true
preview boolNat false       -- some 0
```

## Laws

A lawful isomorphism satisfies:
1. **Back-Forward**: `back (forward s) = s` - round-trip preserves source
2. **Forward-Back**: `forward (back a) = a` - round-trip preserves focus
-/
def iso {s t a b : Type}
    (forward : s → a) (back : b → t) : Iso s t a b :=
  fun {P : Type → Type → Type} [Profunctor P] =>
    Profunctor.dimap (P := P) forward back

/-- Identity optic. -/
def idOptic {α : Type} : Iso' α α :=
  iso (s := α) (t := α) (a := α) (b := α)
    (forward := fun x => x) (back := fun x => x)

/-!
## Lens Construction and Operations
-/

/--
Construct a lens from getter and setter functions.

A lens focuses on exactly one part of a larger structure, allowing you to
view, modify, or replace that part.

## Parameters
- `get`: Extract the focused value from the source
- `set`: Replace the focused value in the source with a new value

## Example

```lean
structure Point where
  x : Int
  y : Int

-- Create a lens focusing on the x coordinate
def xLens : Lens' Point Int :=
  lens' (fun p => p.x) (fun p x' => { p with x := x' })

-- Or more concisely:
def yLens : Lens' Point Int :=
  lens' (·.y) (fun p y' => { p with y := y' })

-- Usage:
let p := Point.mk 10 20
view' xLens p           -- 10
set' xLens 99 p         -- { x := 99, y := 20 }
over' xLens (· + 1) p   -- { x := 11, y := 20 }
```

## Laws

A lawful lens satisfies:
1. **GetPut**: `view l (set l v s) = v` - setting then viewing returns what was set
2. **PutGet**: `set l (view l s) s = s` - setting the current value is a no-op
3. **PutPut**: `set l v (set l v' s) = set l v s` - setting twice is same as setting once
-/
def lens' {s t a b : Type}
    (get : s → a) (set : s → b → t) : Lens s t a b :=
  fun {P} [Profunctor P] [Strong P] pab =>
    let first := Strong.first (P := P) (γ := s) pab
    Profunctor.dimap (P := P)
      (fun s => (get s, s))
      (fun bs => set bs.2 bs.1)
      first

/-- View the focus of a lens. -/
def view' {s a : Type} (l : Lens' s a) (x : s) : a :=
  let forget : Forget a a a := fun a => a
  let result := l (P := fun α β => Forget a α β) forget
  result x

/-- Modify the focus of a lens. -/
def over' {s t a b : Type}
    (l : Lens s t a b) (f : a → b) : s → t :=
  let arrow := FunArrow.mk (α := a) (β := b) f
  let result := l (P := fun α β => FunArrow α β) arrow
  fun s => result s

/-- Set the focus of a lens to a constant value. -/
def set' {s t a b : Type}
    (l : Lens s t a b) (v : b) : s → t :=
  over' l (fun _ => v)

/-- Lens focusing the first component of a pair. -/
def _1 {α β γ : Type} :
    Lens (α × β) (γ × β) α γ :=
  lens' (fun p => p.fst) (fun p b => (b, p.snd))

/-- Lens focusing the second component of a pair. -/
def _2 {α β γ : Type} :
    Lens (α × β) (α × γ) β γ :=
  lens' (fun p => p.snd) (fun p b => (p.fst, b))

/-- Lens that exposes a constant value without modifying the source. -/
def const {s a : Type} (value : a) : Lens' s a :=
  lens' (fun _ => value) (fun s _ => s)

/-!
## Prism Construction and Operations
-/

/--
Construct a prism from a builder and a matcher.

A prism focuses on one case of a sum type (variant), allowing you to
pattern-match to extract a value or construct that variant.

## Parameters
- `build`: Construct a value of the sum type from the focused case
- `split`: Pattern-match on the sum type, returning `Sum.inr a` if the
  focused case is present, or `Sum.inl t` (the unchanged value) otherwise

## Example

```lean
-- Prism for the Some case of Option
def somePrism : Prism' (Option α) α :=
  prism
    (build := some)
    (split := fun opt => match opt with
      | some a => Sum.inr a
      | none => Sum.inl none)

-- Usage:
preview' somePrism (some 42)  -- some 42
preview' somePrism none       -- none
review' somePrism 42          -- some 42
```

## Simpler Alternative

For most cases, `prismFromPartial` is easier to use:

```lean
def somePrism : Prism' (Option α) α :=
  prismFromPartial (match_ := id) (build := some)
```

## Laws

A lawful prism satisfies:
1. **Preview-Review**: `preview p (review p b) = some b` - reviewing then previewing succeeds
2. **Review-Preview**: `preview p s = some a → review p a = s` - if preview succeeds, review reconstructs
-/
def prism {s t a b : Type}
    (build : b → t) (split : s → Sum t a) : Prism s t a b :=
  fun {P} [Profunctor P] [Choice P] pab =>
    let right := Choice.right (P := P) (γ := t) pab
    let post : Sum t b → t :=
      Sum.elim (fun t' => t') (fun b' => build b')
    Profunctor.dimap (P := P) split post right

/-- Attempt to extract a focused value with a prism. -/
def preview' {s a : Type}
    (p : Prism' s a) (x : s) : Option a :=
  let forget : Forget (Option a) a a := fun a => some a
  let result := p (P := fun α β => Forget (Option a) α β) forget
  result x

/-- Inject a value through a prism. -/
def review' {s t a b : Type}
    (p : Prism s t a b) (b₀ : b) : t :=
  p (P := fun α β => Tagged α β) b₀

/--
A prism that always fails to match.

Useful as an identity element when composing prisms with `orElse`,
or when you need a prism that never succeeds.

```lean
preview failing 42  -- none (never matches)
```

Note: `review` on a failing prism will return the default value.
-/
def failing {s a : Type} [Inhabited s] : Prism' s a :=
  prism
    (build := fun _ => default)
    (split := fun s => Sum.inl s)

/--
Create a prism from a partial function (matcher) and a constructor (builder).

This is often more convenient than using `prism` directly with `Sum`.

```lean
-- Prism for even numbers
def evenPrism : Prism' Int Int := prismFromPartial
  (fun n => if n % 2 == 0 then some n else none)
  id

preview evenPrism 4  -- some 4
preview evenPrism 3  -- none
```
-/
def prismFromPartial {s a : Type}
    (match_ : s → Option a) (build : a → s) : Prism' s a :=
  prism
    (build := build)
    (split := fun s =>
      match match_ s with
      | some a => Sum.inr a
      | none => Sum.inl s)

/-!
## Affine Traversal Operations
-/

namespace AffineTraversalOps

/-- Modify the target of an affine traversal. -/
def over {s t a b : Type}
    (aff : Collimator.AffineTraversal s t a b) (f : a → b) : s → t :=
  let arrow := FunArrow.mk (α := a) (β := b) f
  let transformed := aff (P := fun α β => FunArrow α β) arrow
  fun s => transformed s

/-- Set the target of an affine traversal to a constant value. -/
def set {s t a b : Type}
    (aff : Collimator.AffineTraversal s t a b) (value : b) : s → t :=
  over aff (fun _ => value)

/-- Attempt to preview the focused value of an affine traversal. -/
def preview' {s a : Type}
    (aff : Collimator.AffineTraversal' s a) (s₀ : s) : Option a :=
  let forget := fun a : a => some a
  let transformed :=
    aff (P := fun α β => Forget (Option a) α β) forget
  transformed s₀

/-- Every prism is an affine traversal. -/
def ofPrism {s t a b : Type}
    (p : Prism s t a b) : Collimator.AffineTraversal s t a b :=
  fun {P} [Profunctor P] [Strong P] [Choice P] pab =>
    p (P := P) pab

/-- Every lens yields an affine traversal focusing exactly one target. -/
def ofLens {s t a b : Type}
    (l : Lens s t a b) : Collimator.AffineTraversal s t a b :=
  fun {P} [Profunctor P] [Strong P] [Choice P] pab =>
    l (P := P) pab

end AffineTraversalOps

/-!
## Traversal Construction and Operations
-/

/--
Construct a traversal from a polymorphic walker that works for any applicative.

A traversal focuses on zero or more parts of a structure, allowing you to
view all of them, modify all of them, or apply effectful transformations.

## Parameters
- `walk`: A function that applies an effectful transformation `(a → F b)` to all
  focused elements in the structure, threading the applicative effect `F` through.

## Example

```lean
-- Traversal over all elements of a list
def listTraversal : Traversal' (List α) α :=
  traversal fun {F} [Applicative F] f xs =>
    let rec go : List α → F (List α)
      | [] => pure []
      | x :: rest => (· :: ·) <$> f x <*> go rest
    go xs

-- Usage:
let nums := [1, 2, 3, 4]

-- Modify all elements
over listTraversal (· * 2) nums  -- [2, 4, 6, 8]

-- Collect all elements
Fold.toListTraversal listTraversal nums  -- [1, 2, 3, 4]

-- Effectful traversal (e.g., validation)
Traversal.traverse' listTraversal
  (fun n => if n > 0 then some n else none)
  nums  -- some [1, 2, 3, 4]

Traversal.traverse' listTraversal
  (fun n => if n > 0 then some n else none)
  [1, -2, 3]  -- none (short-circuits on first failure)
```

## Laws

A lawful traversal satisfies:
1. **Identity**: `traverse id = id` - traversing with identity is a no-op
2. **Composition**: `traverse (Compose . fmap g . f) = Compose . fmap (traverse g) . traverse f`
-/
def traversal {s t a b : Type}
    (walk : ∀ {F : Type → Type} [Applicative F], (a → F b) → s → F t) :
    Traversal s t a b :=
  fun {P} [Profunctor P] [Strong P] [Choice P] [Wandering P] pab =>
    Wandering.wander (P := P) walk pab

private def traverseList {F : Type → Type} [Applicative F]
    {α β : Type} (f : α → F β) : List α → F (List β)
  | [] => pure []
  | x :: xs => pure List.cons <*> f x <*> traverseList f xs

private def traverseOption {F : Type → Type} [Applicative F]
    {α β : Type} (f : α → F β) : Option α → F (Option β)
  | none => pure none
  | some a => Option.some <$> f a

namespace Traversal

/-- Modify each focus of a traversal. -/
def over' {s t a b : Type}
    (tr : Collimator.Traversal s t a b) (f : a → b) : s → t :=
  let arrow := FunArrow.mk (α := a) (β := b) f
  let transformed := tr (P := fun α β => FunArrow α β) arrow
  fun s => transformed s

/-- Apply an effectful update to each focus of a traversal. -/
def traverse' {s t a b : Type}
    (tr : Collimator.Traversal s t a b)
    {F : Type → Type} [Applicative F]
    (f : a → F b) (s₀ : s) : F t :=
  let star : Star F a b := ⟨f⟩
  let transformed := tr (P := fun α β => Star F α β) star
  transformed s₀

/-- Traversal focusing every element of a list. -/
def eachList {α β : Type} :
    Collimator.Traversal (List α) (List β) α β :=
  Collimator.traversal traverseList

/-- Traversal focusing the value inside an `Option` when present. -/
def eachOption {α β : Type} :
    Collimator.Traversal (Option α) (Option β) α β :=
  Collimator.traversal traverseOption

end Traversal

/-!
## Setter Operations
-/

namespace Setter

/-- Modify the target of a setter. -/
def over' {s t a b : Type}
    (st : Collimator.Setter s t a b) (f : a → b) : s → t :=
  let arrow := FunArrow.mk (α := a) (β := b) f
  let transformed := st (P := fun α β => FunArrow α β) arrow
  fun s => transformed s

/-- Replace the target of a setter with a constant value. -/
def set' {s t a b : Type}
    (st : Collimator.Setter s t a b) (value : b) : s → t :=
  over' st (fun _ => value)

end Setter

/-!
## Foldable Typeclass

`Foldable` captures optics that can extract a list of foci from a structure.
This allows `toList`, `sumOf`, `lengthOf`, etc. to work polymorphically across
`Fold`, `Lens`, `Prism`, `AffineTraversal`, and `Traversal`.
-/

/-- Typeclass for optics that can fold/collect their foci into a list. -/
class Foldable (optic : Type → Type → Type → Type → Type 1) where
  /-- Collect all foci into a list. -/
  foldToList : ∀ {s t a b : Type} [Inhabited (List a)], optic s t a b → s → List a

-- Instance for Fold
instance : Foldable Fold where
  foldToList fld s₀ :=
    let forget : Forget (List _) _ _ := fun x => [x]
    let lifted := fld (P := Forget (List _)) forget
    lifted s₀

-- Instance for Lens
instance : Foldable Lens where
  foldToList l s₀ :=
    let forget : Forget (List _) _ _ := fun x => [x]
    let lifted := l (P := Forget (List _)) forget
    lifted s₀

-- Instance for Prism
instance : Foldable Prism where
  foldToList p s₀ :=
    let forget : Forget (List _) _ _ := fun x => [x]
    let lifted := p (P := Forget (List _)) forget
    lifted s₀

-- Instance for AffineTraversal
instance : Foldable AffineTraversal where
  foldToList aff s₀ :=
    let forget : Forget (List _) _ _ := fun x => [x]
    let lifted := aff (P := Forget (List _)) forget
    lifted s₀

-- Instance for Traversal (uses Wandering instance of Forget)
instance : Foldable Traversal where
  foldToList tr s₀ :=
    let forget : Forget (List _) _ _ := fun x => [x]
    let lifted := tr (P := Forget (List _)) forget
    lifted s₀

-- Instance for Iso
instance : Foldable Iso where
  foldToList i s₀ :=
    let forget : Forget (List _) _ _ := fun x => [x]
    let lifted := i (P := Forget (List _)) forget
    lifted s₀

namespace Fold

/-- Every lens gives a fold that observes its focus. -/
def ofLens {s t a b : Type}
    (l : Lens s t a b) : Collimator.Fold s t a b :=
  fun {P} [Profunctor P] [Strong P] [Choice P] pab => l (P := P) pab

/-- Every affine traversal can be used as a fold. -/
def ofAffine {s t a b : Type}
    (aff : Collimator.AffineTraversal s t a b) : Collimator.Fold s t a b :=
  fun {P} [Profunctor P] [Strong P] [Choice P] pab => aff (P := P) pab

/-
Note: There is no general `Traversal → Fold` coercion because `Traversal` requires
`Wandering P` while `Fold` only provides `Strong P + Choice P`. You cannot construct
a `Wandering` instance from just `Strong + Choice`.

However, for specific operations like `toList`, we use `Forget R` which has a `Wandering`
instance (when R has `One`, `Mul`, `Inhabited`), so traversals work with those functions.

Use `toListTraversal`, `sumOfTraversal`, etc. for traversals, or use the coercion
from `Lens`/`Prism`/`AffineTraversal` to `Fold` for those optic types.
-/

/-- Collect all focuses of a fold into a list. -/
def toList {s a : Type} [Inhabited (List a)]
    (fld : Fold' s a) (s₀ : s) : List a :=
  let forget : Forget (List a) a a := fun x => [x]
  let lifted :=
    fld (P := fun α β => Forget (List a) α β) forget
  lifted s₀

/-- Collect all focuses of a traversal into a list using Forget's Wandering instance. -/
def toListTraversal {s a : Type} [Inhabited (List a)]
    (tr : Traversal' s a) (s₀ : s) : List a :=
  let forget : Forget (List a) a a := fun x => [x]
  let lifted := tr (P := Forget (List a)) forget
  lifted s₀

/-!
## Traversal-specific fold operations

These functions provide the same functionality as the `Fold'` versions but work
directly with `Traversal'`. They use `Forget R` which has a `Wandering` instance.
-/

/-- Check if any focus of a traversal matches a predicate. -/
def anyOfTraversal {s a : Type} [Inhabited (List a)]
    (tr : Traversal' s a) (pred : a → Bool) (s₀ : s) : Bool :=
  (toListTraversal tr s₀).any pred

/-- Check if all foci of a traversal match a predicate. -/
def allOfTraversal {s a : Type} [Inhabited (List a)]
    (tr : Traversal' s a) (pred : a → Bool) (s₀ : s) : Bool :=
  (toListTraversal tr s₀).all pred

/-- Find the first focus of a traversal that matches a predicate. -/
def findOfTraversal {s a : Type} [Inhabited (List a)]
    (tr : Traversal' s a) (pred : a → Bool) (s₀ : s) : Option a :=
  (toListTraversal tr s₀).find? pred

/-- Count the number of foci in a traversal. -/
def lengthOfTraversal {s a : Type} [Inhabited (List a)]
    (tr : Traversal' s a) (s₀ : s) : Nat :=
  (toListTraversal tr s₀).length

/-- Sum all numeric foci of a traversal. -/
def sumOfTraversal {s a : Type} [Inhabited (List a)] [Add a] [OfNat a 0]
    (tr : Traversal' s a) (s₀ : s) : a :=
  (toListTraversal tr s₀).foldl (· + ·) 0

/-- Check if a traversal has no foci. -/
def nullOfTraversal {s a : Type} [Inhabited (List a)]
    (tr : Traversal' s a) (s₀ : s) : Bool :=
  (toListTraversal tr s₀).isEmpty

/-- Compose a lens with a fold to focus deeper. -/
@[inline] def composeLensFold
    {s t a b u v : Type}
    (outer : Lens s t a b) (inner : Collimator.Fold a b u v) :
    Collimator.Fold s t u v :=
  fun {P} [Profunctor P] [Strong P] [Choice P] puv =>
    outer (P := P) (inner (P := P) puv)

/-- Compose two folds to read through nested structures. -/
@[inline] def composeFold
    {s t a b u v : Type}
    (outer : Collimator.Fold s t a b) (inner : Collimator.Fold a b u v) :
    Collimator.Fold s t u v :=
  fun {P} [Profunctor P] [Strong P] [Choice P] puv =>
    outer (P := P) (inner (P := P) puv)

scoped infixr:80 " ∘ₗf " => composeLensFold
scoped infixr:80 " ∘f " => composeFold

/--
Check if any focus of the fold matches a predicate.

```lean
anyOf traversed (· > 3) [1, 2, 5]  -- true
anyOf traversed (· > 10) [1, 2, 5] -- false
```
-/
def anyOf {s a : Type} [Inhabited (List a)]
    (fld : Fold' s a) (pred : a → Bool) (s₀ : s) : Bool :=
  (toList fld s₀).any pred

/--
Check if all foci of the fold match a predicate.

```lean
allOf traversed (· > 0) [1, 2, 3]  -- true
allOf traversed (· > 2) [1, 2, 3]  -- false
```
-/
def allOf {s a : Type} [Inhabited (List a)]
    (fld : Fold' s a) (pred : a → Bool) (s₀ : s) : Bool :=
  (toList fld s₀).all pred

/--
Find the first focus that matches a predicate.

```lean
findOf traversed (· > 2) [1, 2, 3, 4]  -- some 3
findOf traversed (· > 10) [1, 2, 3]    -- none
```
-/
def findOf {s a : Type} [Inhabited (List a)]
    (fld : Fold' s a) (pred : a → Bool) (s₀ : s) : Option a :=
  (toList fld s₀).find? pred

/--
Count the number of foci in the fold.

```lean
lengthOf traversed [1, 2, 3, 4, 5]  -- 5
lengthOf traversed []               -- 0
```
-/
def lengthOf {s a : Type} [Inhabited (List a)]
    (fld : Fold' s a) (s₀ : s) : Nat :=
  (toList fld s₀).length

/--
Sum all numeric foci.

```lean
sumOf traversed [1, 2, 3, 4, 5]  -- 15
```
-/
def sumOf {s a : Type} [Inhabited (List a)] [Add a] [OfNat a 0]
    (fld : Fold' s a) (s₀ : s) : a :=
  (toList fld s₀).foldl (· + ·) 0

/--
Check if the fold has no foci.

```lean
nullOf traversed []       -- true
nullOf traversed [1, 2]   -- false
```
-/
def nullOf {s a : Type} [Inhabited (List a)]
    (fld : Fold' s a) (s₀ : s) : Bool :=
  (toList fld s₀).isEmpty

end Fold

/-!
## Polymorphic Fold Operations

These functions work with any optic that has a `Foldable` instance, including
`Lens`, `Prism`, `AffineTraversal`, `Traversal`, and `Fold`.

Example usage:
```lean
-- All of these work with `toListOf`:
toListOf nameLens person           -- Lens
toListOf somePrism' maybeValue     -- Prism
toListOf affineTraversal structure -- AffineTraversal
toListOf traversed list            -- Traversal
toListOf fold structure            -- Fold
```
-/

/-- Collect all foci of any foldable optic into a list. -/
def toListOf {optic : Type → Type → Type → Type → Type 1} [Foldable optic]
    {s t a b : Type} [Inhabited (List a)] (o : optic s t a b) (s₀ : s) : List a :=
  Foldable.foldToList o s₀

/-- Check if any focus matches a predicate. Works with any foldable optic. -/
def anyOf {optic : Type → Type → Type → Type → Type 1} [Foldable optic]
    {s t a b : Type} [Inhabited (List a)] (o : optic s t a b) (pred : a → Bool) (s₀ : s) : Bool :=
  (toListOf o s₀).any pred

/-- Check if all foci match a predicate. Works with any foldable optic. -/
def allOf {optic : Type → Type → Type → Type → Type 1} [Foldable optic]
    {s t a b : Type} [Inhabited (List a)] (o : optic s t a b) (pred : a → Bool) (s₀ : s) : Bool :=
  (toListOf o s₀).all pred

/-- Find first focus matching a predicate. Works with any foldable optic. -/
def findOf {optic : Type → Type → Type → Type → Type 1} [Foldable optic]
    {s t a b : Type} [Inhabited (List a)] (o : optic s t a b) (pred : a → Bool) (s₀ : s) : Option a :=
  (toListOf o s₀).find? pred

/-- Count the number of foci. Works with any foldable optic. -/
def lengthOf {optic : Type → Type → Type → Type → Type 1} [Foldable optic]
    {s t a b : Type} [Inhabited (List a)] (o : optic s t a b) (s₀ : s) : Nat :=
  (toListOf o s₀).length

/-- Sum all numeric foci. Works with any foldable optic. -/
def sumOf {optic : Type → Type → Type → Type → Type 1} [Foldable optic]
    {s t a b : Type} [Inhabited (List a)] [Add a] [OfNat a 0] (o : optic s t a b) (s₀ : s) : a :=
  (toListOf o s₀).foldl (· + ·) 0

/-- Check if the optic has no foci. Works with any foldable optic. -/
def nullOf {optic : Type → Type → Type → Type → Type 1} [Foldable optic]
    {s t a b : Type} [Inhabited (List a)] (o : optic s t a b) (s₀ : s) : Bool :=
  (toListOf o s₀).isEmpty

/-- Get the first focus if it exists. Works with any foldable optic. -/
def firstOf {optic : Type → Type → Type → Type → Type 1} [Foldable optic]
    {s t a b : Type} [Inhabited (List a)] (o : optic s t a b) (s₀ : s) : Option a :=
  (toListOf o s₀).head?

/-- Get the last focus if it exists. Works with any foldable optic. -/
def lastOf {optic : Type → Type → Type → Type → Type 1} [Foldable optic]
    {s t a b : Type} [Inhabited (List a)] (o : optic s t a b) (s₀ : s) : Option a :=
  (toListOf o s₀).getLast?

/-!
## Getter Optic

A Getter is a read-only optic that focuses on exactly one value.
It's simpler than a Lens because it doesn't require a setter.

Getters are useful when you only need to extract data from a structure
without the ability to modify it.

## Encoding

Unlike other optics, Getters are best encoded directly as getter functions,
since profunctor encodings don't add meaningful structure for read-only operations.

The key operation is `view`, which extracts the focus from the source.
-/

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

/-!
## Review Optic

A Review is a write-only optic for constructing values.
It's the dual of Getter - while Getter extracts values, Review constructs them.

Reviews are useful when you only need to build a value from a focus
without the ability to pattern match on it.

## Encoding

Unlike other optics, Reviews are best encoded directly as construction functions,
since profunctor encodings don't add meaningful structure for write-only operations.

The key operation is `review`, which constructs a target from a focus value.
-/

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
    p (P := Tagged) b⟩

/--
Every Iso can be used as a Review (forgetful conversion).
Uses the Tagged profunctor to extract just the backward function.
-/
def Review.ofIso {s t a b : Type} (i : Iso s t a b) : Review t b :=
  ⟨fun b =>
    i (P := Tagged) b⟩

/--
Compose two Reviews.
-/
def Review.compose {t u v : Type}
    (outer : Review t u) (inner : Review u v) : Review t v :=
  ⟨fun v => outer.build (inner.build v)⟩

end Collimator
