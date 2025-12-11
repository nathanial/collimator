import Collimator.Optics
import Collimator.Combinators

/-!
# Collimator Operators

Infix operators for optic operations:
- `∘` - standard function composition (works naturally with type alias optics!)
- `^.` - view (for lenses)
- `^?` - preview (for prisms/affine)
- `%~` - over (modify)
- `.~` - set
- `&` - reverse application
- `optic%` - type-annotated optic definition

## Composition

With type alias optics, standard function composition (`∘`) works naturally:

```lean
-- Compose two lenses
let composed := outerLens ∘ innerLens

-- Compose a lens with a prism (gives AffineTraversal)
let affine := myLens ∘ myPrism

-- Compose a lens with a traversal (gives Traversal)
let trav := myLens ∘ myTraversal
```

The profunctor constraints are automatically propagated by Lean's type system.
No special composition operator or typeclass is needed!

## Type Inference for Composed Optics

**Inline composition works without annotations** when used directly with operations:

```lean
-- These work - the operation provides type context
over' (traversed ∘ nameLens ∘ addressLens) f data
view' (outerLens ∘ innerLens) data
```

**Named optics need type annotations** because Lean can't infer the profunctor type:

```lean
-- This may fail with "stuck typeclass" error:
-- def myOptic := traversed ∘ nameLens ∘ addressLens

-- Use optic% to add the type annotation cleanly:
def myOptic := optic% traversed ∘ nameLens ∘ addressLens : Traversal' Company String
```

The `optic%` macro simply wraps the expression with a type annotation, providing
the context Lean needs to resolve the profunctor constraints.
-/

namespace Collimator.Operators

open Collimator
open Collimator.Setter
open Collimator.Combinators


/-!
## Operators

### Operator Quick Reference

| Operator | Name | Usage | Description |
|----------|------|-------|-------------|
| `^.` | view | `s ^. lens` | Extract the focused value |
| `^?` | preview | `s ^? prism` | Extract if present (returns `Option`) |
| `%~` | over | `lens %~ f` | Modify with a function (use with `&`) |
| `.~` | set | `lens .~ v` | Replace with a value (use with `&`) |
| `&` | pipe | `s & lens .~ v` | Reverse application for chaining |
| `∘` | compose | `lens1 ∘ lens2` | Standard function composition |

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

-- Composition (use standard ∘)
let composed := outerLens ∘ innerLens
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

Extracts the focused value from the source. Works with Lens' and Iso'.

```lean
let point := Point.mk 10 20
point ^. xLens  -- 10

-- Composed access
let nested := { outer := { inner := 42 } }
nested ^. (outerLens ∘ innerLens)  -- 42
```
-/
scoped syntax:60 term:61 " ^. " term:61 : term
scoped macro_rules
  | `($s ^. $l) => `(Collimator.view' $l $s)

/--
Preview through a prism using infix notation.

Attempts to extract the focused value, returning `Option`. Returns `some`
if the prism matches, `none` otherwise. Works with Prism', AffineTraversal'.

```lean
(some 42) ^? somePrism'    -- some 42
none ^? somePrism'         -- none

-- Safe head access
[1, 2, 3] ^? _head         -- some 1
[] ^? _head                -- none
```
-/
scoped syntax:60 term:61 " ^? " term:61 : term
scoped macro_rules
  | `($s ^? $p) => `(Collimator.preview' $p $s)

/--
Modify the focus of a setter-like optic.

Returns a function `s → s` that modifies the focused part(s). Use with `&`
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
scoped syntax:80 term:81 " %~ " term:81 : term
scoped macro_rules
  | `($optic %~ $f) => `(Collimator.over' $optic $f)

/--
Set the focus of a setter-like optic to a constant value.

Returns a function `s → s` that replaces the focused part(s). Use with `&`
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
scoped syntax:80 term:81 " .~ " term:81 : term
scoped macro_rules
  | `($optic .~ $value) => `(Collimator.set' $optic $value)

/--
Define a composed optic with an explicit type annotation.

When composing optics, Lean sometimes can't infer the profunctor type parameter.
This macro provides a clean syntax for adding the required type annotation.

```lean
-- Instead of:
def myOptic : Traversal' (List Person) String :=
  traversed ∘ nameLens ∘ addressLens

-- Write:
def myOptic := optic% traversed ∘ nameLens ∘ addressLens : Traversal' (List Person) String

-- Multi-line for complex chains:
def complexOptic := optic%
  departmentsLens ∘ traversed ∘ employeesLens ∘ traversed ∘ salaryLens
  : Traversal' Company Int
```

Note: This is only needed when defining named optics. Inline usage with
`view'`, `over'`, etc. works without annotations because those operations
provide the necessary type context.
-/
scoped macro "optic%" e:term ":" t:term : term => `(($e : $t))

end Collimator.Operators
