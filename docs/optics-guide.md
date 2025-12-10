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
6. [Quick Reference](#quick-reference)

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
