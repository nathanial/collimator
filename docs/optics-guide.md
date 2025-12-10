# The Complete Guide to Optics in Collimator

Welcome! This guide explains every optic type and typeclass in the Collimator library. We assume no prior knowledge of optics or profunctors - just basic Lean familiarity.

## Table of Contents

1. [What Are Optics?](#what-are-optics)
2. [The Big Picture](#the-big-picture)
3. [Optic Types](#optic-types)
   - [Lens](#lens---exactly-one-focus)
   - [Prism](#prism---maybe-one-focus)
   - [Iso](#iso---perfect-two-way-conversion)
   - [Traversal](#traversal---zero-or-more-foci)
   - [AffineTraversal](#affinetraversal---at-most-one-focus)
   - [Fold](#fold---read-only-multiple-foci)
   - [Setter](#setter---write-only)
   - [Getter](#getter---read-only-single-focus)
   - [Review](#review---construction-only)
4. [The Optic Hierarchy](#the-optic-hierarchy)
5. [Profunctor Typeclasses](#profunctor-typeclasses-the-theory)
6. [Advanced Combinators](#advanced-combinators)
   - [Filtering](#filtering-combinators)
   - [Indexed Optics](#indexed-optics)
   - [List Operations](#list-operations)
   - [Bitraversals](#bitraversals)
   - [Plated (Recursive Structures)](#plated-recursive-structures)
   - [Prism Combinators](#prism-combinators)
7. [Container Instances](#container-instances)
8. [Debug & Integration](#debug--integration)
9. [Quick Reference](#quick-reference)

---

## What Are Optics?

Optics are composable tools for accessing and modifying parts of data structures. Think of them as "programmable getters and setters" that you can combine like LEGO blocks.

**The Problem They Solve:**

Imagine you have nested data:

```lean
structure Address where
  city : String
  zip : String

structure Person where
  name : String
  address : Address
```

To update a person's city, you'd write:

```lean
def updateCity (p : Person) (newCity : String) : Person :=
  { p with address := { p.address with city := newCity } }
```

This is tedious and gets worse with deeper nesting. With optics:

```lean
def personCity : Lens' Person String :=
  personAddress ⊚ addressCity

-- Now updating is simple:
set personCity "Boston" alice
over personCity String.toUpper alice  -- modify with a function
view personCity alice                  -- read the value
```

**Key Benefits:**
- **Composable**: Chain optics with `⊚` to reach deep into structures
- **Reusable**: Define once, use everywhere
- **Type-safe**: The compiler ensures your optics are valid
- **Polymorphic**: One optic works with `view`, `set`, `over`, `traverse`, etc.

---

## The Big Picture

There are several kinds of optics, each for different situations:

| Optic | What it focuses on | Example |
|-------|-------------------|---------|
| **Lens** | Exactly one thing (always present) | A field in a struct |
| **Prism** | Maybe one thing (might be absent) | The `some` case of `Option` |
| **Iso** | A perfect two-way conversion | `String ↔ List Char` |
| **Traversal** | Zero or more things | All elements in a list |
| **AffineTraversal** | Zero or one thing | First element of a list |
| **Fold** | Zero or more (read-only) | Collecting values |
| **Setter** | Zero or more (write-only) | Bulk updates |
| **Getter** | Exactly one (read-only) | A computed property |
| **Review** | Construction only | Building a value |

---

## Optic Types

### Lens - Exactly One Focus

A **Lens** focuses on exactly one part of a structure that is always present.

**When to use:** Accessing fields in structs/records.

```lean
-- A lens from Person to their name
def personName : Lens' Person String :=
  lens' (·.name) (fun p n => { p with name := n })
```

**Operations:**

```lean
-- Read the focus
view personName alice           -- "Alice"

-- Replace the focus
set personName "Alicia" alice   -- { name := "Alicia", ... }

-- Modify with a function
over personName String.toUpper alice  -- { name := "ALICE", ... }
```

**Operators:**

```lean
alice ^. personName              -- view: "Alice"
alice & personName .~ "Alicia"   -- set: { name := "Alicia", ... }
alice & personName %~ String.toUpper  -- over: { name := "ALICE", ... }
```

**Composition:**

```lean
-- Compose two lenses to reach nested data
def personCity : Lens' Person String :=
  personAddress ⊚ addressCity

-- Now you can access the city directly
alice ^. personCity              -- "Boston"
alice & personCity .~ "Seattle"  -- updates nested city
```

**The Laws (what makes a lens valid):**

1. **Get-Put**: If you set what you just got, nothing changes
   ```lean
   set l (view l s) s = s
   ```

2. **Put-Get**: If you get what you just set, you get that value
   ```lean
   view l (set l v s) = v
   ```

3. **Put-Put**: Setting twice is the same as setting once (with the second value)
   ```lean
   set l v2 (set l v1 s) = set l v2 s
   ```

---

### Prism - Maybe One Focus

A **Prism** focuses on one case of a sum type (like `Option` or a union). The focus might not exist.

**When to use:** Pattern matching on variants, optional values, or constructors.

```lean
-- A prism focusing on the Some case of Option
def somePrism : Prism' (Option α) α :=
  prism some (fun opt => match opt with
    | some a => Sum.inr a
    | none => Sum.inl none)
```

**Operations:**

```lean
-- Try to extract (returns Option because focus might not exist)
preview somePrism (some 42)     -- some 42
preview somePrism none          -- none

-- Construct a value from the focus
review somePrism 42             -- some 42

-- Modify if the focus exists
over somePrism (· + 1) (some 42)  -- some 43
over somePrism (· + 1) none       -- none (unchanged)
```

**Key Insight:** Prisms are "smart constructors" that can also deconstruct:
- `review` builds a value
- `preview` tries to take it apart

**Real-World Example:**

```lean
-- Focus on the Left case of Sum
def leftPrism : Prism' (Sum α β) α := ...

-- Focus on JSON number values
def jsonNumber : Prism' JsonValue Float := ...

-- Chain: get the number from a JSON value in an Option
def optJsonNum := somePrism ⊚ jsonNumber
preview optJsonNum (some (JsonValue.number 3.14))  -- some 3.14
```

---

### Iso - Perfect Two-Way Conversion

An **Iso** (isomorphism) represents a lossless, reversible conversion between two types.

**When to use:** Type conversions where no information is lost.

```lean
-- String is isomorphic to List Char
def chars : Iso' String (List Char) :=
  iso String.toList String.mk

-- Swap pair components
def swapped : Iso' (α × β) (β × α) :=
  iso (fun (a, b) => (b, a)) (fun (b, a) => (a, b))
```

**Operations:**

```lean
-- Convert forward
view chars "hello"              -- ['h', 'e', 'l', 'l', 'o']

-- Convert backward (using review)
review chars ['h', 'i']         -- "hi"

-- Modify through the iso
over chars List.reverse "hello" -- "olleh"
```

**Key Property:** An Iso can be used as ANY other optic. It's the most powerful optic type.

**The Laws:**

1. **Round-trip forward**: `view iso (review iso a) = a`
2. **Round-trip backward**: `review iso (view iso s) = s`

---

### Traversal - Zero or More Foci

A **Traversal** focuses on multiple parts of a structure (possibly zero).

**When to use:** Operating on all elements of a collection, or multiple fields at once.

```lean
-- Focus on all elements of a list
def traversed : Traversal' (List α) α := ...

-- Use it to modify all elements
over traversed (· * 2) [1, 2, 3]    -- [2, 4, 6]

-- Collect all foci into a list
toListOf traversed [1, 2, 3]       -- [1, 2, 3]
```

**Composition with Lenses:**

```lean
-- Focus on all employee salaries in a company
def allSalaries : Traversal' Company Int :=
  companyDepts ⊚ traversed ⊚ deptEmployees ⊚ traversed ⊚ empSalary

-- Give everyone a 10% raise
over allSalaries (fun s => s + s / 10) company

-- Get total payroll
sumOf allSalaries company
```

**Effectful Traversal:**

```lean
-- Traverse with IO effects
traverse allSalaries (fun s => do
  IO.println s!"Processing salary: {s}"
  pure (s + 1000)
) company
```

**Fold Operations on Traversals:**

```lean
toListOf traversal source    -- collect all foci
sumOf traversal source       -- sum numeric foci
lengthOf traversal source    -- count foci
anyOf traversal pred source  -- any match predicate?
allOf traversal pred source  -- all match predicate?
findOf traversal pred source -- find first matching
```

---

### AffineTraversal - At Most One Focus

An **AffineTraversal** focuses on zero or one element. It's between a Lens (exactly one) and a Traversal (zero or more).

**When to use:** Optional fields, safe indexing, partial matches.

```lean
-- Safe head of a list (might not exist)
def _head : AffineTraversal' (List α) α := ...

-- Composing Prism with Lens gives AffineTraversal
def contactCity : AffineTraversal' Contact String :=
  contactAddress ⊚ somePrism ⊚ addressCity
```

**Operations:**

```lean
-- Preview (like Prism)
preview _head [1, 2, 3]        -- some 1
preview _head []               -- none

-- Modify if present
over _head (· + 10) [1, 2, 3]  -- [11, 2, 3]
over _head (· + 10) []         -- []
```

**Why it exists:** When you compose a Prism with a Lens (or vice versa), you get an AffineTraversal. It can't be a Lens (focus might be absent) or a Prism (no natural `review`).

---

### Fold - Read-Only Multiple Foci

A **Fold** is a read-only traversal. It can focus on multiple elements but can only extract, not modify.

**When to use:** Queries, aggregations, collecting data.

```lean
-- All folds support these operations:
toList fold source           -- collect into list
anyOf fold predicate source  -- any match?
allOf fold predicate source  -- all match?
findOf fold predicate source -- find first match
lengthOf fold source         -- count foci
sumOf fold source            -- sum (for numeric types)
nullOf fold source           -- is it empty?
firstOf fold source          -- first focus (Option)
lastOf fold source           -- last focus (Option)
```

**Why Fold exists separately:** Sometimes you have a way to extract multiple values but no sensible way to put them back. For example, getting all keys from a map, or all nodes in a tree traversal.

---

### Setter - Write-Only

A **Setter** can modify values but cannot read them.

**When to use:** Rare - usually you want a Lens or Traversal. Setters are mostly theoretical.

```lean
over setter f source   -- modify
set setter value source -- replace
-- No view/preview operations!
```

---

### Getter - Read-Only Single Focus

A **Getter** extracts exactly one value but cannot modify it.

**When to use:** Computed properties, derived values.

```lean
-- A getter for the full name (computed from first + last)
def fullName : Getter Person String :=
  getter (fun p => p.firstName ++ " " ++ p.lastName)

Getter.view fullName alice  -- "Alice Smith"
```

**Note:** Unlike other optics, Getter is not profunctor-encoded. It's a simple wrapper around a function.

---

### Review - Construction Only

A **Review** can only construct values, not extract them. It's the dual of Getter.

**When to use:** Smart constructors, building values.

```lean
-- Review for constructing Some values
def someReview : Review (Option α) α :=
  mkReview some

Review.review someReview 42  -- some 42
```

---

## The Optic Hierarchy

Optics form a hierarchy based on their capabilities. An optic higher in the hierarchy can be used wherever a lower one is expected:

```
              Iso
             /   \
          Lens   Prism
             \   /
        AffineTraversal
              |
          Traversal
           /     \
        Fold    Setter
```

**What this means:**
- An `Iso` can be used as a `Lens`, `Prism`, or any other optic
- A `Lens` can be used as an `AffineTraversal`, `Traversal`, `Fold`, or `Setter`
- A `Prism` can be used as an `AffineTraversal`, `Traversal`, or `Fold`
- etc.

**In code:**

```lean
-- This function takes a Fold, but you can pass a Lens, Traversal, etc.
def countFoci (fold : Fold' s a) (source : s) : Nat :=
  lengthOf fold source

-- All of these work:
countFoci traversed [1, 2, 3]     -- Traversal as Fold
countFoci personName alice        -- Lens as Fold
countFoci somePrism (some 42)     -- Prism as Fold
```

---

## Profunctor Typeclasses (The Theory)

*This section explains HOW optics work internally. You don't need this to USE optics, but it helps understand error messages and the design.*

### What's a Profunctor?

A **Profunctor** is a type constructor `P : Type → Type → Type` that is:
- **Contravariant** in its first argument (consumes values)
- **Covariant** in its second argument (produces values)

```lean
class Profunctor (P : Type → Type → Type) where
  dimap : (α' → α) → (β → β') → P α β → P α' β'
```

**The key insight:** Functions `α → β` form a profunctor!
- `dimap f g h = g ∘ h ∘ f` (pre-compose with f, post-compose with g)

### How Optics Use Profunctors

An optic is a function that works for ALL profunctors satisfying certain constraints:

```lean
-- A Lens works with any profunctor that has Strong
structure Lens (s t a b : Type) : Type 1 where
  toLens : ∀ {P} [Profunctor P], Strong P → P a b → P s t
```

By choosing different concrete profunctors, we get different operations:
- `Forget R` (ignores second type) → `view` operation
- `FunArrow` (plain functions) → `over` operation
- `Star F` (effectful functions) → `traverse` operation
- `Tagged` (ignores first type) → `review` operation

### The Profunctor Hierarchy

Each typeclass adds capabilities:

#### Profunctor (Base)
```lean
class Profunctor (P : Type → Type → Type) where
  dimap : (α' → α) → (β → β') → P α β → P α' β'
```
Can transform inputs and outputs.

#### Strong (Products)
```lean
class Strong (P) [Profunctor P] where
  first : P α β → P (α × γ) (β × γ)
```
Can work with one component of a pair, leaving the other unchanged. **Enables Lenses.**

#### Choice (Sums)
```lean
class Choice (P) [Profunctor P] where
  left : P α β → P (Sum α γ) (Sum β γ)
```
Can work with one branch of a sum type. **Enables Prisms.**

#### Wandering (Traversals)
```lean
class Wandering (P) [Profunctor P] [Strong P] [Choice P] where
  wander : (∀ {F} [Applicative F], (α → F β) → σ → F τ) → P α β → P σ τ
```
Can traverse any structure compatible with Applicative. **Enables Traversals.**

#### Closed (Functions)
```lean
class Closed (P) [Profunctor P] where
  closed : P α β → P (γ → α) (γ → β)
```
Can work inside function types. Used for advanced optics.

### Why This Design?

This "profunctor optics" encoding has key advantages:

1. **Composition is just function composition**: `lens1 ⊚ lens2` chains naturally
2. **Type-safe**: The profunctor constraints ensure only valid operations compile
3. **Extensible**: New optic types can be added by defining new constraints
4. **Efficient**: No intermediate data structures when composing

---

## Advanced Combinators

Collimator provides powerful combinators for real-world scenarios that go beyond basic optics.

### Filtering Combinators

Filter which elements a traversal focuses on based on predicates.

**`filtered`** - Restrict any traversal to elements matching a predicate:

```lean
import Collimator.Combinators.Filtered
open Collimator.Combinators

-- Double only positive numbers in a list
over (filtered traversed (· > 0)) (· * 2) [-1, 2, -3, 4]
-- Result: [-1, 4, -3, 8]

-- Works with any traversal
over (filtered employeeTraversal (·.department == "Engineering"))
     (fun e => { e with salary := e.salary * 110 / 100 })
     company
```

**`filteredList`** - Shorthand for `filtered traversed`:

```lean
-- These are equivalent:
over (filteredList (· > 0)) (· * 2) nums
over (filtered traversed (· > 0)) (· * 2) nums
```

**`ifilteredList`** - Filter with access to both index and value:

```lean
-- Modify only elements at even indices
over (ifilteredList fun i _ => i % 2 == 0) (· ++ "!") ["a", "b", "c", "d"]
-- Result: ["a!", "b", "c!", "d"]

-- Modify elements where index equals value
over (ifilteredList fun i v => i == v) (· * 10) [0, 5, 2, 3, 8]
-- Result: [0, 5, 20, 30, 8]
```

---

### Indexed Optics

Access elements by their position/key in a container.

**`HasIx` typeclass** - Focus on a single indexed position (0-or-1 focus):

```lean
import Collimator.Combinators.Indexed
open Collimator.Indexed

-- Modify element at index 2
over (ix 2) (· * 10) [1, 2, 3, 4, 5]
-- Result: [1, 2, 30, 4, 5]

-- Out of bounds is a no-op
over (ix 10) (· * 10) [1, 2, 3]
-- Result: [1, 2, 3]
```

**`HasAt` typeclass** - Lens to optional element at index:

```lean
-- Get optional element
view' (atLens 1) ["a", "b", "c"]   -- some "b"
view' (atLens 5) ["a", "b", "c"]   -- none

-- Can also be used to delete by setting to none
set' (atLens 1) none ["a", "b", "c"]  -- ["a", "c"] (depending on impl)
```

**`itraversed`** - Traverse with index information:

```lean
import Collimator.Instances.List
open Collimator.Instances.List

-- Get (index, value) pairs
toListOf itraversed ["a", "b", "c"]
-- [(0, "a"), (1, "b"), (2, "c")]

-- Modify values using their indices
over itraversed (fun (i, v) => (i, s!"{i}: {v}")) ["a", "b"]
-- [(0, "0: a"), (1, "1: b")]
```

**Available instances:**

| Container | `ix` | `atLens` | `itraversed` | `traversed` |
|-----------|------|----------|--------------|-------------|
| `List α`  | `Nat` | `Nat` | Yes | Yes |
| `Array α` | `Nat` | `Nat` | Yes | Yes |
| `String`  | `Nat` | `Nat` | Yes | Yes |
| `Option α`| `Unit`| `Unit`| No | No |

---

### List Operations

Safe operations on list structure without runtime errors.

**`_head`** - Safely access the first element (AffineTraversal):

```lean
import Collimator.Combinators.ListOps
open Collimator.Combinators

preview _head [1, 2, 3]        -- some 1
preview _head ([] : List Int)  -- none

over _head (· * 10) [1, 2, 3]  -- [10, 2, 3]
over _head (· * 10) []         -- []
```

**`_last`** - Safely access the last element:

```lean
preview _last [1, 2, 3]        -- some 3
over _last (· * 10) [1, 2, 3]  -- [1, 2, 30]
```

**`taking n`** - Traverse only the first `n` elements:

```lean
over (taking 2) (· * 10) [1, 2, 3, 4]  -- [10, 20, 3, 4]
over (taking 0) (· * 10) [1, 2, 3]     -- [1, 2, 3]
over (taking 10) (· * 10) [1, 2]       -- [10, 20]

toListOf (taking 3) [1, 2, 3, 4, 5]    -- [1, 2, 3]
```

**`dropping n`** - Skip the first `n` elements, traverse the rest:

```lean
over (dropping 2) (· * 10) [1, 2, 3, 4]  -- [1, 2, 30, 40]
toListOf (dropping 2) [1, 2, 3, 4, 5]    -- [3, 4, 5]
```

---

### Bitraversals

Work with both components of pairs or either branch of sums.

```lean
import Collimator.Combinators.Bitraversal
open Collimator.Combinators.Bitraversal
```

**`both`** - Traverse both components of a homogeneous pair `(α × α)`:

```lean
-- Double both components
over both (· * 2) (3, 5)
-- (6, 10)

-- Collect both values
toListOf both (1, 2)
-- [1, 2]

-- Works with any type
over both String.toUpper ("hello", "world")
-- ("HELLO", "WORLD")
```

**`beside`** - Traverse elements in both parts of a pair using separate traversals:

```lean
-- Traverse all elements in both lists
let listPair := ([1, 2], [3, 4, 5])
over (beside traversed traversed) (· + 1) listPair
-- ([2, 3], [4, 5, 6])

-- Collect all elements from both sides
toListOf (beside traversed traversed) (["a", "b"], ["c"])
-- ["a", "b", "c"]

-- Works with different container types on each side
let mixed := (some 5, [1, 2])
over (beside somePrism traversed) (· * 10) mixed
-- (some 50, [10, 20])
```

**`chosen`** - Traverse whichever branch of `Sum α α` is present:

```lean
over chosen (· * 2) (Sum.inl 5)   -- Sum.inl 10
over chosen (· * 2) (Sum.inr 7)   -- Sum.inr 14

preview chosen (Sum.inl "hi")     -- some "hi"
preview chosen (Sum.inr "bye")    -- some "bye"
```

**`swapped` / `swappedSum`** - Swap components:

```lean
view swapped (1, 2)                -- (2, 1)
view swappedSum (Sum.inl 42)       -- Sum.inr 42
view swappedSum (Sum.inr 99)       -- Sum.inl 99
```

---

### Plated (Recursive Structures)

The `Plated` typeclass enables powerful operations on recursive data structures.

```lean
import Collimator.Combinators.Plated
open Collimator.Combinators.Plated
```

**Defining a Plated instance:**

```lean
inductive Tree (α : Type) where
  | leaf : α → Tree α
  | node : Tree α → Tree α → Tree α

-- plate focuses on immediate children of the same type
instance : Plated (Tree α) where
  plate := traversal fun f t =>
    match t with
    | Tree.leaf _ => pure t  -- leaves have no Tree children
    | Tree.node l r => pure Tree.node <*> f l <*> f r
```

**`transform`** - Bottom-up transformation (children first, then parent):

```lean
-- Simplify arithmetic expressions
def simplify : Expr → Expr
  | Expr.add (Expr.num 0) e => e  -- 0 + e → e
  | Expr.add e (Expr.num 0) => e  -- e + 0 → e
  | e => e

-- Apply simplify to ALL subexpressions, bottom-up
transform simplify expr
```

**`rewrite`** - Iteratively rewrite until no more changes:

```lean
-- Keep simplifying until fixpoint
def trySimplify : Expr → Option Expr
  | Expr.add (Expr.num 0) e => some e
  | _ => none

rewrite trySimplify complexExpr
```

**`universeList`** - Collect all descendants (transitive closure):

```lean
-- Get all subexpressions
universeList myExpr
-- [myExpr, child1, child2, grandchild1, grandchild2, ...]
```

**Other Plated operations:**

```lean
-- Children only (not recursive)
childrenOf node           -- immediate children
overChildren f node       -- transform immediate children

-- Queries
cosmosCount tree          -- total node count
depth tree               -- maximum depth
allOf predicate tree     -- all nodes satisfy predicate?
anyOf predicate tree     -- any node satisfies predicate?
findOf predicate tree    -- first matching node (Option)

-- Top-down variants
transformDown f tree     -- apply f first, then recurse
rewriteDown f tree       -- try f first, then recurse
```

**Built-in instances:**

```lean
-- List is plated: children are tail sublists
instance : Plated (List α)

-- Option has no recursive structure
instance : Plated (Option α)
```

---

### Prism Combinators

Additional operations for working with prisms.

```lean
import Collimator.Combinators.PrismOps
open Collimator.Combinators
```

**`orElse`** - Try the first prism, fall back to the second:

```lean
-- Match either pattern
def evenOrDiv3 : AffineTraversal' Int Int :=
  orElse evenPrism div3Prism

preview evenOrDiv3 4   -- some 4 (even)
preview evenOrDiv3 9   -- some 9 (div by 3)
preview evenOrDiv3 7   -- none (neither)
```

**`affineFromPartial`** - Build an AffineTraversal from preview/set:

```lean
def safeHead : AffineTraversal' (List a) a :=
  affineFromPartial
    (fun xs => xs.head?)
    (fun xs a => match xs with
      | [] => []
      | _ :: rest => a :: rest)
```

**`prismFromPartial`** (in `Collimator.Prelude`):

```lean
-- Create a prism from a partial function
def evenPrism : Prism' Int Int :=
  prismFromPartial
    (fun n => if n % 2 == 0 then some n else none)
    id  -- review function

preview evenPrism 4  -- some 4
preview evenPrism 3  -- none
review evenPrism 4   -- 4
```

**`failing`** - A prism that never matches:

```lean
preview failing x  -- always none
over failing f x   -- always unchanged (identity)
```

---

## Container Instances

Collimator provides optics for common Lean containers.

### List

```lean
import Collimator.Instances.List
open Collimator.Instances.List

-- Traverse all elements
over traversed (· + 1) [1, 2, 3]  -- [2, 3, 4]

-- Indexed traversal
toListOf itraversed ["a", "b"]   -- [(0, "a"), (1, "b")]

-- Index access
over (ix 1) String.toUpper ["a", "b", "c"]  -- ["a", "B", "c"]
view' (atLens 0) [1, 2, 3]                  -- some 1
```

### Array

```lean
import Collimator.Instances.Array
open Collimator.Instances.Array

-- Same API as List
over traversed (· * 2) #[1, 2, 3]  -- #[2, 4, 6]
over (ix 0) (· + 100) #[1, 2, 3]   -- #[101, 2, 3]
```

### Option

```lean
import Collimator.Instances.Option
open Collimator.Instances.Option

-- Focus on the Some case
preview somePrism' (some 42)  -- some 42
preview somePrism' none       -- none
review somePrism' 42          -- some 42

-- Modify if present
over somePrism' (· + 1) (some 42)  -- some 43
over somePrism' (· + 1) none       -- none
```

### String

```lean
import Collimator.Instances.String
open Collimator.Instances.String

-- String ↔ List Char isomorphism
view chars "hello"            -- ['h', 'e', 'l', 'l', 'o']
review chars ['h', 'i']       -- "hi"

-- Traverse characters
over traversed Char.toUpper "hello"  -- "HELLO"

-- Indexed access
over (ix 0) Char.toUpper "hello"     -- "Hello"
view' (atLens 0) "abc"               -- some 'a'
```

### Sum

```lean
import Collimator.Instances.Sum
open Collimator.Instances.Sum

-- Focus on left or right branch
preview left' (Sum.inl 42 : Sum Int String)   -- some 42
preview left' (Sum.inr "hi" : Sum Int String) -- none
preview right' (Sum.inr "hi")                 -- some "hi"
```

### Prod (Tuples)

```lean
-- Built into core Collimator
view _1 (1, "hello")    -- 1
view _2 (1, "hello")    -- "hello"
set _1 99 (1, "hello")  -- (99, "hello")

-- Or use helpers with explicit types
import Collimator.Helpers
open Collimator.Helpers

view' (first' Int String) (1, "hello")   -- 1
view' (second' Int String) (1, "hello")  -- "hello"
```

---

## Debug & Integration

### Debug Utilities

Trace optic operations for debugging.

```lean
import Collimator.Debug
open Collimator.Debug

-- Wrap a lens to log operations
let debugLens := tracedLens "myLens" myLens

view' debugLens myStruct
-- Prints: [myLens] view → <value>

set' debugLens 42 myStruct
-- Prints: [myLens] set ← 42

-- Same for prisms
let debugPrism := tracedPrism "somePrism" somePrism'
preview' debugPrism (some 42)
-- Prints: [somePrism] preview some 42 → some 42
```

**Runtime Law Checking:**

```lean
import Collimator.Debug.LawCheck

-- Verify lens laws at runtime
verifyLensLaws "myLens" myLens testValue [val1, val2, val3]
-- Prints: ✓ myLens: All lens laws verified (3 samples)

-- Individual law checks
checkGetPut myLens value testStruct     -- Bool
checkPutGet myLens value testStruct     -- Bool
checkPutPut myLens v1 v2 testStruct     -- Bool

-- Prism laws
verifyPrismLaws "somePrism" somePrism' [val1, val2]

-- Iso laws
verifyIsoLaws "chars" charsIso [str1, str2]
```

### Error Guidance

Safe operations with better error messages.

```lean
import Collimator.Poly.Guidance
open Collimator.Poly.Guidance

-- Safe view that returns Option
viewSafe somePrism value          -- some x or none

-- View with default value
viewOrElse somePrism "default" value

-- Check if focus exists
hasFocus somePrism value          -- Bool

-- Get informative error message
prismViewError "somePrism"
-- "Cannot use 'view' with Prism 'somePrism': prisms may not match. Use 'preview' instead."
```

### Integration Patterns

Combine optics with Lean's monad transformers.

```lean
import Collimator.Integration
open Collimator.Integration

-- Validate through a lens (Except)
def validateAge : Int → Except String Int
  | n => if n >= 0 then .ok n else .error "Age must be non-negative"

validateThrough ageLens validateAge person
-- .ok updatedPerson or .error "Age must be non-negative"

-- Extract with custom error
previewOrError somePrism "Value not present" maybeValue
-- .ok value or .error "Value not present"

-- StateM integration
getThrough lens         -- read focused value from state
setThrough lens value   -- write focused value to state
modifyThrough lens f    -- modify focused value in state
zoom lens action        -- run action on focused substate

-- ReaderM integration
askThrough lens         -- read focused value from environment
localThrough lens f action  -- modify environment for action
```

---

## Quick Reference

### Creating Optics

```lean
-- Lens: getter and setter
lens' (·.field) (fun s v => { s with field := v })

-- Prism: constructor and matcher
prism build (fun s => match s with | Pattern a => .inr a | _ => .inl s)

-- Iso: bidirectional conversion
iso forward backward

-- Traversal: applicative traversal function
traversal (fun f list => list.mapM f)
```

### Operations

| Operation | Works On | Returns | Description |
|-----------|----------|---------|-------------|
| `view` | Lens, Iso, Getter | `a` | Extract focus |
| `set` | Lens, Prism, Traversal, ... | `s` | Replace focus |
| `over` | Lens, Prism, Traversal, ... | `s` | Modify focus |
| `preview` | Prism, AffineTraversal | `Option a` | Try to extract |
| `review` | Prism, Iso, Review | `t` | Construct value |
| `traverse` | Traversal | `F t` | Effectful traversal |
| `toListOf` | Any readable optic | `List a` | Collect all foci |

### Operators

| Operator | Meaning | Example |
|----------|---------|---------|
| `⊚` | Compose optics | `lens1 ⊚ lens2` |
| `^.` | View (monomorphic) | `s ^. lens` |
| `^.'` | View (for composed) | `s ^.' (l1 ⊚ l2)` |
| `.~` | Set | `s & lens .~ value` |
| `%~` | Over (modify) | `s & lens %~ f` |
| `&` | Reverse application | `s & lens .~ v & lens2 %~ f` |

### Composition Results

| Outer | Inner | Result |
|-------|-------|--------|
| Iso | Iso | Iso |
| Iso | Lens | Lens |
| Iso | Prism | Prism |
| Lens | Lens | Lens |
| Lens | Prism | AffineTraversal |
| Prism | Lens | AffineTraversal |
| Prism | Prism | Prism |
| Lens | Traversal | Traversal |
| Traversal | Lens | Traversal |
| Traversal | Traversal | Traversal |
| * | Traversal | Traversal |
| Traversal | * | Traversal |

---

## Next Steps

- See `docs/cheatsheet.md` for a quick reference card
- See `docs/tutorial.md` for a hands-on tutorial
- See `examples/` for real-world usage patterns
- See `docs/performance.md` for optimization tips

Happy focusing!
