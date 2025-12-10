import Collimator.Core.Profunctor
import Collimator.Core.Strong
import Collimator.Optics.Types
import Collimator.Concrete.Forget
import Collimator.Concrete.FunArrow

namespace Collimator

open Collimator.Core
open Collimator.Concrete

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

end Collimator
