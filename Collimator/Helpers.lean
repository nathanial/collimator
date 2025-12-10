import Collimator.Optics
import Collimator.Instances

/-!
# Type Inference Helpers

These functions provide better type inference by partially applying
common optics, reducing the need for explicit type annotations.

## The Problem

Polymorphic optics like `_1` often require explicit type annotations:
```lean
let lens := _1 (α := Nat) (β := String) (γ := Nat)
```

## The Solution

Use helper functions that fix the types you know:
```lean
let lens := first' Nat String  -- Lens' (Nat × String) Nat
```

Or use inference-friendly constructors:
```lean
def myLens := lensOf Point Int (·.x) (fun p x => { p with x := x })
```
-/

namespace Collimator.Helpers

open Collimator
open Collimator.Core


/-! ## Tuple Lens Helpers -/

/-- First element lens when you know both element types.

```lean
-- Instead of: _1 (α := Nat) (β := String) (γ := Nat)
-- Use: first' Nat String
```
-/
@[inline] def first' (α β : Type) : Lens' (α × β) α := _1

/-- Second element lens when you know both element types.

```lean
-- Instead of: _2 (α := Nat) (β := String) (γ := String)
-- Use: second' Nat String
```
-/
@[inline] def second' (α β : Type) : Lens' (α × β) β := _2

/-! ## Inference-Friendly Builders -/

/-- Build a monomorphic lens with explicit source and focus types.

Better inference than `lens'` when types are known at the definition site.

```lean
structure Point where
  x : Int
  y : Int

def xLens : Lens' Point Int := lensOf Point Int
  (get := fun p => p.x)
  (set := fun p v => { p with x := v })
```
-/
@[inline] def lensOf (S A : Type) (get : S → A) (set : S → A → S) : Lens' S A :=
  lens' get set

/-- Build a polymorphic lens with all types explicit. -/
@[inline] def lensOfPoly (S T A B : Type) (get : S → A) (set : S → B → T) : Lens S T A B :=
  lens' get set

/-- Build a monomorphic prism with explicit source and focus types.

```lean
def evenPrism : Prism' Int Int := prismOf Int Int
  (build := id)
  (match_ := fun n => if n % 2 == 0 then some n else none)
```
-/
@[inline] def prismOf (S A : Type) (build : A → S) (match_ : S → Option A) : Prism' S A :=
  prism (build := build) (split := fun s =>
    match match_ s with
    | some a => Sum.inr a
    | none => Sum.inl s)

/-! ## Common Optics with Types Explicit -/

/-- Option.some prism with element type specified.

```lean
-- Instead of: somePrism (α := Int) (β := Int)
-- Or: somePrism' (α := Int)
-- Use: some' Int
```
-/
@[inline] def some' (α : Type) : Prism' (Option α) α :=
  Collimator.Instances.Option.somePrism' α

/-- List element traversal with element type specified.

```lean
-- Instead of: traversed (α := Int)
-- Use: each' Int
```
-/
@[inline] def each' (α : Type) : Traversal' (List α) α :=
  Collimator.Instances.List.traversed

/-! ## Re-exports for Convenience -/

-- Re-export tuple lenses for namespace convenience
export Collimator (_1 _2 lens' prism)

end Collimator.Helpers
