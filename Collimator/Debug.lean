import Collimator.Optics
import Collimator.Combinators

/-!
# Debug Utilities for Collimator Optics

This module provides debugging utilities for optics development:
- **Traced optics**: Wrap any optic to log operations to stderr
- **Law checking**: Runtime verification of optic laws

## Usage

```lean
import Collimator.Debug

-- Wrap a lens to trace all operations
let debugLens := tracedLens "myLens" myLens
let result := view' debugLens myStruct
-- Prints: [myLens] view → <value>
```
-/

namespace Collimator.Debug

open Collimator


/--
Wrap a lens to trace view and set operations.

When the traced lens is used, it prints debug information to stderr:
- `[name] view → <value>` when viewing
- `[name] set ← <value>` when setting

## Example

```lean
structure Point where x : Int; y : Int
deriving Repr

def xLens : Lens' Point Int := lens' (·.x) (fun p v => { p with x := v })

let traced := tracedLens "xLens" xLens
let p := Point.mk 10 20

view' traced p
-- Prints: [xLens] view → 10

set' traced 99 p
-- Prints: [xLens] set ← 99
```
-/
def tracedLens {s a : Type} (name : String) (l : Lens' s a) [Repr a] : Lens' s a :=
  lens'
    (fun s =>
      let result := view' l s
      dbg_trace s!"[{name}] view → {repr result}"
      result)
    (fun s v =>
      dbg_trace s!"[{name}] set ← {repr v}"
      set' l v s)

/--
Wrap a prism to trace preview and review operations.

When the traced prism is used, it prints debug information to stderr:
- `[name] preview <source> → some <value>` or `→ none` when previewing
- `[name] review <value> → <result>` when reviewing

## Example

```lean
let traced := tracedPrism "somePrism" (somePrism' Int)

preview' traced (some 42)
-- Prints: [somePrism] preview some 42 → some 42

preview' traced none
-- Prints: [somePrism] preview none → none

review' traced 99
-- Prints: [somePrism] review 99 → some 99
```
-/
def tracedPrism {s a : Type} (name : String) (p : Prism' s a) [Repr a] [Repr s] : Prism' s a :=
  prismFromPartial
    (fun s =>
      let result := preview' p s
      let resultStr := match result with
        | some v => s!"some {repr v}"
        | none => "none"
      dbg_trace s!"[{name}] preview {repr s} → {resultStr}"
      result)
    (fun a =>
      let result := review' p a
      dbg_trace s!"[{name}] review {repr a} → {repr result}"
      result)

end Collimator.Debug
