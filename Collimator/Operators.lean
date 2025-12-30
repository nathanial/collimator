import Collimator.Optics
import Collimator.Combinators
import Collimator.Concrete.FunArrow
import Collimator.Concrete.Forget

/-!
# Collimator Operators

Haskell-style infix operators for optic operations. These operators work
uniformly across all optic types (Lens, Traversal, Prism, AffineTraversal)
thanks to automatic coercion to concrete optic types.

## Operators

| Operator | Name | Usage | Works with |
|----------|------|-------|------------|
| `^.` | view | `s ^. lens` | Lens |
| `^?` | preview | `s ^? prism` | Prism, AffineTraversal |
| `^??` | previewOrElse | `s ^?? prism \| def` | Prism, AffineTraversal |
| `^..` | toList | `s ^.. trav` | Traversal, Fold |
| `%~` | over | `optic %~ f` | Lens, Traversal, Prism, AffineTraversal |
| `.~` | set | `optic .~ v` | Lens, Traversal, Prism, AffineTraversal |
| `&` | pipe | `s & optic .~ v` | (reverse application for chaining) |
| `∘` | compose | `lens1 ∘ lens2` | All optics (standard function composition) |

## Examples

```lean
open scoped Collimator.Operators

-- View through a lens
point ^. xLens                    -- 10

-- Modify through a lens
point & xLens %~ (· + 1)          -- increment x

-- Set through a lens
point & xLens .~ 99               -- replace x with 99

-- Chain multiple updates
point & xLens .~ 100 & yLens %~ (· + 5)

-- Modify ALL elements through a traversal
[1, 2, 3] & traversed %~ (· * 2)  -- [2, 4, 6]

-- Collect all elements through a traversal
[(1, "a"), (2, "b")] ^.. (traversed ∘ _1)  -- [1, 2]

-- Preview through a prism (returns Option)
(some 42) ^? somePrism'           -- some 42
none ^? somePrism'                -- none

-- Modify through a prism (only affects matching case)
(some 42) & somePrism' %~ (· + 1) -- some 43
```

## How It Works

The operators work across all optic types by coercing polymorphic optics to
concrete types. For example, `%~` coerces any settable optic to `ASetter`:

```
ASetter s t a b = FunArrow a b → FunArrow s t
```

This is the same approach used by Haskell's lens library.
-/

namespace Collimator.Operators

open Collimator
open Collimator.Core
open Collimator.Concrete
open Collimator.Combinators

/-!
## Concrete Optic Types

These types instantiate the profunctor parameter to specific concrete profunctors,
enabling uniform operations across all optic types via coercion.
-/

/-- Concrete setter type - any optic that can modify values. -/
abbrev ASetter (s t a b : Type) := FunArrow a b → FunArrow s t

/-- Concrete getter type - optics that can extract exactly one value. -/
abbrev AGetter (s a : Type) := Forget a a a → Forget a s s

/-- Concrete preview type - optics that can extract zero or one value. -/
abbrev APreview (s a : Type) := Forget (Option a) a a → Forget (Option a) s s

/-!
## Coercion Instances

These instances allow automatic coercion from polymorphic optics to concrete types.
-/

-- ASetter coercions (for %~ and .~)
instance : Coe (Lens s t a b) (ASetter s t a b) where
  coe l := fun fab => l (P := FunArrow) fab

instance : Coe (Traversal s t a b) (ASetter s t a b) where
  coe tr := fun fab => tr (P := FunArrow) fab

instance : Coe (AffineTraversal s t a b) (ASetter s t a b) where
  coe aff := fun fab => aff (P := FunArrow) fab

instance : Coe (Prism s t a b) (ASetter s t a b) where
  coe p := fun fab => p (P := FunArrow) fab

instance : Coe (Iso s t a b) (ASetter s t a b) where
  coe i := fun fab => i (P := FunArrow) fab

-- AGetter coercions (for ^.)
instance : Coe (Lens' s a) (AGetter s a) where
  coe l := fun faa => l (P := Forget a) faa

instance : Coe (Iso' s a) (AGetter s a) where
  coe i := fun faa => i (P := Forget a) faa

-- APreview coercions (for ^?)
instance : Coe (Prism' s a) (APreview s a) where
  coe p := fun faa => p (P := Forget (Option a)) faa

instance : Coe (AffineTraversal' s a) (APreview s a) where
  coe aff := fun faa => aff (P := Forget (Option a)) faa

-- Prism to AffineTraversal coercion (for composition)
instance : Coe (Prism s t a b) (AffineTraversal s t a b) where
  coe p := fun {P} [Profunctor P] [Strong P] [Choice P] pab => p (P := P) pab

instance : Coe (Prism' s a) (AffineTraversal' s a) where
  coe p := fun {P} [Profunctor P] [Strong P] [Choice P] pab => p (P := P) pab

-- Lens to AffineTraversal coercion (for composition)
instance : Coe (Lens s t a b) (AffineTraversal s t a b) where
  coe l := fun {P} [Profunctor P] [Strong P] [Choice P] pab => l (P := P) pab

instance : Coe (Lens' s a) (AffineTraversal' s a) where
  coe l := fun {P} [Profunctor P] [Strong P] [Choice P] pab => l (P := P) pab

/-!
## Universal Operation Functions

These functions work on concrete optic types and are used by the operators.
-/

/-- Modify through any settable optic. -/
def overU {s t a b : Type} (setter : ASetter s t a b) (f : a → b) (x : s) : t :=
  (setter (FunArrow.mk f)).run x

/-- Set through any settable optic. -/
def setU {s t a b : Type} (setter : ASetter s t a b) (v : b) (x : s) : t :=
  overU setter (fun _ => v) x

/-- View through a getter (exactly one focus). -/
def viewU {s a : Type} (getter : AGetter s a) (x : s) : a :=
  getter id x

/-- Preview through a prism or affine (zero or one focus). -/
def previewU {s a : Type} (previewer : APreview s a) (x : s) : Option a :=
  previewer some x

/-- Preview through a prism or affine, returning a default if no focus. -/
def previewOrElseU {s a : Type} (previewer : APreview s a) (x : s) (default : a) : a :=
  (previewer some x).getD default

/-- Collect all foci through a traversal. -/
def toListU {s a : Type} [Inhabited (List a)] (tr : Traversal' s a) (x : s) : List a :=
  Fold.toListTraversal tr x

/-!
## Operators
-/

/--
Reverse function application, useful for chaining optic operators.

```lean
-- Instead of: setU xLens 10 (setU yLens 20 point)
-- Write:      point & xLens .~ 10 & yLens .~ 20
```
-/
scoped infixl:10 " & " => fun x f => f x

/--
View through a lens using infix notation.

Extracts the focused value from the source. Works with `Lens'` and `Iso'`.

```lean
point ^. xLens  -- 10

-- Composed access
nested ^. (outerLens ∘ innerLens)  -- 42
```
-/
scoped syntax:60 term:61 " ^. " term:61 : term
scoped macro_rules
  | `($s ^. $l) => `(viewU $l $s)

/--
Preview through a prism or affine traversal using infix notation.

Attempts to extract the focused value, returning `Option`. Returns `some`
if the optic matches, `none` otherwise.

```lean
(some 42) ^? somePrism'    -- some 42
none ^? somePrism'         -- none

-- Safe indexed access
[1, 2, 3] ^? headAffine    -- some 1
[] ^? headAffine           -- none
```
-/
scoped syntax:60 term:61 " ^? " term:61 : term
scoped macro_rules
  | `($s ^? $p) => `(previewU $p $s)

/--
Preview through a prism or affine traversal with a default value.

Returns the focused value if present, otherwise returns the default.
This eliminates the need for pattern matching on `Option` after preview.

```lean
(some 42) ^?? somePrism' | 0     -- 42
none ^?? somePrism' | 0          -- 0

-- Safe indexed access with default
[1, 2, 3] ^?? _head | 99         -- 1
[] ^?? _head | 99                -- 99

-- HashMap access with default
world ^?? chunkAt pos | defaultChunk
```
-/
scoped syntax:60 term:61 " ^?? " term:61 " | " term:61 : term
scoped macro_rules
  | `($s ^?? $p | $default) => `(previewOrElseU $p $s $default)

/--
Collect all foci through a traversal as a list.

```lean
[1, 2, 3] ^.. traversed                    -- [1, 2, 3]
[(1, "a"), (2, "b")] ^.. (traversed ∘ _1)  -- [1, 2]
```
-/
scoped syntax:60 term:61 " ^.. " term:61 : term
scoped macro_rules
  | `($s ^.. $t) => `(toListU $t $s)

/--
Modify the focus of any settable optic.

Works with Lens, Traversal, Prism, AffineTraversal, and Iso.
Returns a function `s → t` that modifies the focused part(s).
Use with `&` for fluent syntax.

```lean
-- Modify single field (Lens)
point & xLens %~ (· + 1)

-- Modify all elements (Traversal)
[1, 2, 3] & traversed %~ (· * 2)   -- [2, 4, 6]

-- Modify if present (Prism)
(some 42) & somePrism' %~ (· + 1)  -- some 43

-- Chained modifications
point & xLens %~ (· * 2) & yLens %~ (· + 10)
```
-/
scoped syntax:80 term:81 " %~ " term:81 : term
scoped macro_rules
  | `($optic %~ $f) => `(overU $optic $f)

/--
Set the focus of any settable optic to a constant value.

Works with Lens, Traversal, Prism, AffineTraversal, and Iso.
Returns a function `s → t` that replaces the focused part(s).
Use with `&` for fluent syntax.

```lean
-- Set single field (Lens)
point & xLens .~ 100

-- Set all elements (Traversal)
[1, 2, 3] & traversed .~ 0         -- [0, 0, 0]

-- Set if present (Prism)
(some 42) & somePrism' .~ 99       -- some 99

-- Chained sets
point & xLens .~ 10 & yLens .~ 20
```
-/
scoped syntax:80 term:81 " .~ " term:81 : term
scoped macro_rules
  | `($optic .~ $value) => `(setU $optic $value)

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
operators works without annotations because the operations provide type context.
-/
scoped macro "optic%" e:term ":" t:term : term => `(($e : $t))

end Collimator.Operators


/-!
## Field Lens Elaborator

The `fieldLens%` elaborator creates lenses for structure fields with minimal boilerplate.
-/

open Lean Elab Term

/--
Create a lens for a structure field.

This elaborator generates the getter/setter boilerplate for a field lens:

```lean
-- Instead of:
def nameLens : Lens' Person String :=
  lens' (fun p => p.name) (fun p v => { p with name := v })

-- Write:
def nameLens : Lens' Person String := fieldLens% Person name
```

The elaborator generates: `lens' (·.field) (fun s v => { s with field := v })`

Note: A type annotation is typically needed for proper type inference.
-/
elab "fieldLens%" _structName:ident fieldName:ident : term => do
  let fieldNameId := fieldName.getId

  -- Generate the lens code as a string and parse it.
  -- This works around Lean's syntax limitations with struct update syntax,
  -- where the field name position requires special `structInstLVal` syntax
  -- that can't be easily spliced via quotation.
  let code := s!"Collimator.lens' (·.{fieldNameId}) (fun s v => \{ s with {fieldNameId} := v })"

  let env ← getEnv
  let stx ← match Lean.Parser.runParserCategory env `term code with
    | .ok stx => pure stx
    | .error e => throwError "fieldLens% parse error: {e}"

  elabTerm stx none

/-!
## Constructor Prism Elaborator

The `ctorPrism%` elaborator creates prisms for inductive type constructors with minimal boilerplate.
-/

/--
Create a prism for an inductive type constructor.

This elaborator generates the review/preview boilerplate for a constructor prism:

```lean
-- Instead of:
def strConfigPrism : Prism' ConfigValue String :=
  prism (fun s => ConfigValue.str s)
        (fun v => match v with
         | ConfigValue.str s => Sum.inr s
         | other => Sum.inl other)

-- Write:
def strConfigPrism : Prism' ConfigValue String := ctorPrism% ConfigValue.str
```

The elaborator generates:
```
prism Constructor (fun s => match s with
  | Constructor x => Sum.inr x
  | other => Sum.inl other)
```

Supports constructors with:
- Single argument: `ConfigValue.str` → focuses on `String`
- Multiple arguments: `Address.domestic` → focuses on tuple `(String × String)`
- No arguments: `JsonValue.null` → focuses on `Unit`

Note: A type annotation is typically needed for proper type inference.
-/
elab "ctorPrism%" ctorName:ident : term => do
  let ctorNameId := ctorName.getId
  let env ← getEnv

  -- Resolve the constructor name in the current scope
  let resolvedName ← resolveGlobalConstNoOverload ctorName

  -- Look up constructor info to determine arity
  let some ctorInfo := env.find? resolvedName
    | throwError "ctorPrism%: unknown constructor '{ctorNameId}'"

  let numParams ← match ctorInfo with
    | .ctorInfo ci => pure ci.numFields
    | _ => throwError "ctorPrism%: '{ctorNameId}' is not a constructor"

  -- Use the original identifier string (works in scope since we're in the same module)
  let ctorStr := toString ctorNameId
  -- Generate code based on arity
  let code ← match numParams with
    | 0 =>
      -- Zero args: focus on Unit
      pure s!"Collimator.prism (fun () => {ctorStr}) (fun s => match s with | {ctorStr} => Sum.inr () | other => Sum.inl other)"
    | 1 =>
      -- Single arg: focus on the value directly
      pure s!"Collimator.prism {ctorStr} (fun s => match s with | {ctorStr} x => Sum.inr x | other => Sum.inl other)"
    | n =>
      -- Multiple args: focus on a tuple
      -- Generate: x0, x1, x2, ...
      let vars := (List.range n).map (fun i => s!"x{i}")
      let varList := String.intercalate ", " vars
      -- Pattern: Constructor x0 x1 x2
      let pattern := s!"{ctorStr} " ++ String.intercalate " " vars
      -- Tuple construction: (x0, x1, x2)
      let tuple := s!"({varList})"
      -- Tuple deconstruction in lambda: fun (x0, x1, x2) => Constructor x0 x1 x2
      let review := s!"(fun {tuple} => {pattern})"
      pure s!"Collimator.prism {review} (fun s => match s with | {pattern} => Sum.inr {tuple} | other => Sum.inl other)"

  let stx ← match Lean.Parser.runParserCategory env `term code with
    | .ok stx => pure stx
    | .error e => throwError "ctorPrism% parse error: {e}"

  elabTerm stx none
