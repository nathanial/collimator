import Collimator.Optics

/-!
# Integration Patterns

Utilities for integrating Collimator optics with common Lean 4 patterns:
- `Except` for error handling
- `StateM` for stateful updates
- `ReaderM` for configuration

## Usage

```lean
import Collimator.Prelude
import Collimator.Integration

open Collimator.Integration

-- Validate through a lens
let result := validateThrough nameLens validateName person

-- Stateful modification
let ((), newState) := modifyThrough ageLens (modify (· + 1)) state |>.run initialState
```
-/

namespace Collimator.Integration

open Collimator

/-! ## Except/Result Integration -/

/--
Validate and update a focus through a lens.

If validation succeeds, the focus is replaced with the validated value.
If validation fails, the error is propagated.

```lean
def validateAge : Int → Except String Int
  | n => if n >= 0 then pure n else throw "Age must be non-negative"

validateThrough ageLens validateAge person
-- Returns Except.ok with updated person, or Except.error with message
```
-/
def validateThrough {s a e : Type}
    (l : Lens' s a) (validate : a → Except e a) (s₀ : s) : Except e s :=
  match validate (view' l s₀) with
  | .ok a' => .ok (set' l a' s₀)
  | .error err => .error err

/--
Try to extract through a prism, with custom error on failure.
-/
def previewOrError {s a e : Type}
    (p : Prism' s a) (err : e) (s₀ : s) : Except e a :=
  match preview' p s₀ with
  | some a => .ok a
  | none => .error err

/--
Traverse with validation, failing on first invalid element.
-/
def validateAll {s a e : Type}
    (t : Traversal' s a) (validate : a → Except e a) (s₀ : s) : Except e s :=
  Traversal.traverse' t validate s₀

/-! ## StateM Integration -/

/--
Modify a focus using a stateful computation.

The state monad operates on the focused value, and the result
is written back through the lens.

```lean
def incrementAndReturn : StateM Int Int := do
  let n ← get
  set (n + 1)
  pure n

-- Run stateful computation on the focused value
modifyThrough xLens incrementAndReturn point
-- Returns (old value, point with incremented x)
```
-/
def modifyThrough {s a r : Type}
    (l : Lens' s a) (action : StateM a r) : StateM s r := do
  let currentS ← get
  let focused := view' l currentS
  let (result, newFocused) := action.run focused
  set (set' l newFocused currentS)
  pure result

/--
Get a focused value within StateM.
-/
def getThrough {s a : Type} (l : Lens' s a) : StateM s a := do
  let s ← get
  pure (view' l s)

/--
Set a focused value within StateM.
-/
def setThrough {s a : Type} (l : Lens' s a) (v : a) : StateM s Unit := do
  let s ← get
  set (set' l v s)

/--
Modify a focused value within StateM.
-/
def overThrough {s a : Type} (l : Lens' s a) (f : a → a) : StateM s Unit := do
  let s ← get
  set (over' l f s)

/--
Zoom into a focus for a block of stateful operations.
All StateM operations within the block operate on the focused value.
-/
def zoom {s a r : Type} (l : Lens' s a) (action : StateM a r) : StateM s r := do
  let s ← get
  let focused := view' l s
  let (result, newFocused) := action.run focused
  set (set' l newFocused s)
  pure result

/-! ## ReaderM Integration -/

/--
Read a focused value from the reader environment.
-/
def askThrough {s a : Type} (l : Lens' s a) : ReaderM s a := do
  let s ← read
  pure (view' l s)

/--
Run a computation with a modified environment through a lens.
-/
def localThrough {s a r : Type}
    (l : Lens' s a) (f : a → a) (action : ReaderM s r) : ReaderM s r := do
  let s ← read
  let newS := over' l f s
  ReaderT.adapt (fun _ => newS) action

/-! ## Option/Maybe Integration -/

/--
Update through a prism only if the pattern matches.
Returns the updated structure or the original if pattern didn't match.
-/
def updateWhenMatches {s a : Type}
    (p : Prism' s a) (f : a → a) : s → s :=
  fun s₀ =>
    match preview' p s₀ with
    | some a => review' p (f a)
    | none => s₀

/--
Transform a prism into a function that returns Sum.
-/
def prismToSum {s a : Type} (p : Prism' s a) (s₀ : s) : Sum s a :=
  match preview' p s₀ with
  | some a => Sum.inr a
  | none => Sum.inl s₀

/-! ## Traversal Utilities -/

/--
Filter and transform through a traversal in one pass.
-/
def mapMaybe {s a : Type}
    (t : Traversal' s a) (f : a → Option a) (s₀ : s) : s :=
  Traversal.over' t (fun a => f a |>.getD a) s₀

/--
Traverse with Option monad, short-circuiting on None.
-/
def traverseOption {s a b : Type}
    (t : Traversal s s a b) (f : a → Option b) (s₀ : s) : Option s :=
  Traversal.traverse' t f s₀

end Collimator.Integration
