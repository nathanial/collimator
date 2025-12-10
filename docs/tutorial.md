# Collimator Tutorial

A progressive introduction to profunctor optics in Lean 4.

## Table of Contents

1. [Your First Lens](#1-your-first-lens)
2. [Composing Optics](#2-composing-optics)
3. [Working with Optional Data](#3-working-with-optional-data)
4. [Traversing Collections](#4-traversing-collections)
5. [Real-World Patterns](#5-real-world-patterns)

---

## 1. Your First Lens

A **lens** focuses on a single field within a structure. It lets you:
- **View** the field's value
- **Set** the field to a new value
- **Modify** the field with a function

### Defining a Structure

```lean
structure Point where
  x : Int
  y : Int
  deriving Repr
```

### Creating Lenses Manually

```lean
import Collimator.Prelude

-- A lens focusing on the x field
def xLens : Lens' Point Int :=
  lens' (get := fun p => p.x) (set := fun p x' => { p with x := x' })

-- A lens focusing on the y field
def yLens : Lens' Point Int :=
  lens' (·.y) (fun p y' => { p with y := y' })
```

### Using Lenses

```lean
open scoped Collimator.Operators

def example1 : IO Unit := do
  let p := Point.mk 10 20

  -- View: extract the focused value
  IO.println s!"x = {view xLens p}"           -- x = 10
  IO.println s!"x = {p ^. xLens}"             -- operator syntax

  -- Set: replace the focused value
  let p2 := set xLens 100 p
  let p3 := p & xLens .~ 100                  -- operator syntax
  IO.println s!"after set: {repr p2}"         -- { x := 100, y := 20 }

  -- Over: modify the focused value with a function
  let p4 := over xLens (· * 2) p
  let p5 := p & xLens %~ (· * 2)              -- operator syntax
  IO.println s!"after over: {repr p4}"        -- { x := 20, y := 20 }
```

### Auto-generating Lenses

For structures with many fields, use `makeLenses`:

```lean
-- File: MyTypes.lean
structure Person where
  name : String
  age : Nat
  email : String

-- File: MyLenses.lean (must be separate file!)
import MyTypes
import Collimator.Derive.Lenses

open Collimator.Derive in
makeLenses Person

-- Generates:
-- personName : Lens' Person String
-- personAge : Lens' Person Nat
-- personEmail : Lens' Person String
```

---

## 2. Composing Optics

The real power of optics comes from composition. Use the `⊚` operator (or `∘` in ASCII) to compose optics that focus deeper into nested structures.

### Nested Structures

```lean
structure Address where
  street : String
  city : String
  zipCode : String

structure Employee where
  name : String
  salary : Int
  address : Address

structure Department where
  name : String
  employees : List Employee

structure Company where
  name : String
  departments : List Department
```

### Defining Nested Lenses

```lean
-- Address lenses
def streetLens : Lens' Address String := lens' (·.street) (fun a s => { a with street := s })
def cityLens : Lens' Address String := lens' (·.city) (fun a c => { a with city := c })

-- Employee lenses
def empNameLens : Lens' Employee String := lens' (·.name) (fun e n => { e with name := n })
def salaryLens : Lens' Employee Int := lens' (·.salary) (fun e s => { e with salary := s })
def addressLens : Lens' Employee Address := lens' (·.address) (fun e a => { e with address := a })

-- Compose to reach nested fields
def empCityLens : Lens' Employee String := addressLens ⊚ cityLens
```

### Using Composed Lenses

```lean
def example2 : IO Unit := do
  let emp := Employee.mk "Alice" 75000 (Address.mk "123 Main St" "Boston" "02101")

  -- View nested field
  IO.println s!"City: {view empCityLens emp}"           -- City: Boston
  IO.println s!"City: {emp ^. addressLens ⊚ cityLens}"  -- same with operators

  -- Modify nested field
  let emp2 := over empCityLens String.toUpper emp
  IO.println s!"New city: {view empCityLens emp2}"      -- New city: BOSTON

  -- Chain modifications with &
  let emp3 := emp
    & salaryLens %~ (· + 5000)
    & addressLens ⊚ cityLens .~ "New York"
  IO.println s!"Salary: {emp3 ^. salaryLens}, City: {emp3 ^. empCityLens}"
```

### Composition Type Rules

When you compose optics, the result type depends on what you're combining:

| Outer | Inner | Result |
|-------|-------|--------|
| Lens | Lens | Lens |
| Lens | Prism | AffineTraversal |
| Lens | Traversal | Traversal |
| Prism | Prism | Prism |
| Prism | Lens | AffineTraversal |
| Traversal | anything | Traversal |

---

## 3. Working with Optional Data

**Prisms** focus on data that may or may not be present. They're perfect for:
- `Option` types (Some vs None)
- Sum types (Either/variants)
- Pattern matching scenarios

### Prisms for Option

```lean
import Collimator.Instances.Option

def example3a : IO Unit := do
  let maybeNum : Option Int := some 42
  let nothing : Option Int := none

  -- preview: extract if present (returns Option)
  IO.println s!"{preview somePrism' maybeNum}"    -- some 42
  IO.println s!"{maybeNum ^? somePrism'}"         -- operator syntax
  IO.println s!"{nothing ^? somePrism'}"          -- none

  -- over: modify if present, otherwise no-op
  let doubled := over somePrism' (· * 2) maybeNum
  IO.println s!"{doubled}"                        -- some 84

  -- review: construct a value (inject into the sum type)
  let created := review somePrism' 100
  IO.println s!"{created}"                        -- some 100
```

### Prisms for Sum Types

```lean
import Collimator.Instances.Sum

-- Focus on the Left case
def leftPrism : Prism' (Sum String Int) String := left'
-- Focus on the Right case
def rightPrism : Prism' (Sum String Int) Int := right'

def example3b : IO Unit := do
  let val1 : Sum String Int := Sum.inl "error"
  let val2 : Sum String Int := Sum.inr 42

  IO.println s!"{val1 ^? leftPrism}"              -- some "error"
  IO.println s!"{val1 ^? rightPrism}"             -- none
  IO.println s!"{val2 ^? rightPrism}"             -- some 42

  -- Construct values
  let err := review leftPrism "failed"            -- Sum.inl "failed"
  let ok := review rightPrism 100                 -- Sum.inr 100
```

### Creating Custom Prisms

```lean
-- Prism that focuses on positive numbers
def positivePrism : Prism' Int Int :=
  prismFromPartial
    (match_ := fun n => if n > 0 then some n else none)
    (build := id)

def example3c : IO Unit := do
  IO.println s!"{5 ^? positivePrism}"             -- some 5
  IO.println s!"{(-3) ^? positivePrism}"          -- none
  IO.println s!"{over positivePrism (· * 2) 5}"   -- 10
  IO.println s!"{over positivePrism (· * 2) (-3)}" -- -3 (unchanged)
```

### Composing with Prisms

When you compose a lens with a prism, you get an `AffineTraversal` (0 or 1 focus):

```lean
structure Config where
  apiKey : Option String
  timeout : Nat

def apiKeyLens : Lens' Config (Option String) :=
  lens' (·.apiKey) (fun c k => { c with apiKey := k })

-- Compose lens with prism to optionally access the string inside
def apiKeyValue : AffineTraversal' Config String := apiKeyLens ⊚ somePrism'

def example3d : IO Unit := do
  let config1 := Config.mk (some "secret123") 30
  let config2 := Config.mk none 30

  IO.println s!"{config1 ^? apiKeyValue}"         -- some "secret123"
  IO.println s!"{config2 ^? apiKeyValue}"         -- none

  -- Safely modify if present
  let config3 := over apiKeyValue String.toUpper config1
  IO.println s!"{config3 ^? apiKeyValue}"         -- some "SECRET123"
```

---

## 4. Traversing Collections

**Traversals** focus on multiple elements at once. They're used for:
- All elements of a list or array
- All matching elements (filtered)
- Effectful transformations

### Basic Traversal

```lean
import Collimator.Instances.List

def example4a : IO Unit := do
  let nums := [1, 2, 3, 4, 5]

  -- Collect all foci as a list
  IO.println s!"{Fold.toList traversed nums}"     -- [1, 2, 3, 4, 5]

  -- Modify all elements
  let doubled := over traversed (· * 2) nums
  IO.println s!"{doubled}"                        -- [2, 4, 6, 8, 10]

  -- Use fold helpers
  IO.println s!"Any > 3? {anyOf traversed (· > 3) nums}"   -- true
  IO.println s!"All > 0? {allOf traversed (· > 0) nums}"   -- true
  IO.println s!"Count: {lengthOf traversed nums}"          -- 5
```

### Filtered Traversal

Focus only on elements matching a predicate:

```lean
import Collimator.Combinators.Filtered

def example4b : IO Unit := do
  let nums := [-1, 2, -3, 4, -5, 6]

  -- Double only positive numbers
  let result := over (filteredList (· > 0)) (· * 2) nums
  IO.println s!"{result}"                         -- [-1, 4, -3, 8, -5, 12]

  -- Collect only negatives
  let negatives := Fold.toList (filteredList (· < 0)) nums
  IO.println s!"{negatives}"                      -- [-1, -3, -5]
```

### Safe List Access

Use `_head` and `_last` for safe access (returns `AffineTraversal`):

```lean
import Collimator.Combinators.ListOps

def example4c : IO Unit := do
  let nums := [1, 2, 3]
  let empty : List Int := []

  -- Safe head access
  IO.println s!"{preview _head nums}"             -- some 1
  IO.println s!"{preview _head empty}"            -- none

  -- Modify head if present
  let modified := over _head (· * 10) nums
  IO.println s!"{modified}"                       -- [10, 2, 3]

  -- taking and dropping
  let first2 := over (taking 2) (· * 10) [1, 2, 3, 4]
  IO.println s!"{first2}"                         -- [10, 20, 3, 4]

  let last2 := over (dropping 2) (· * 10) [1, 2, 3, 4]
  IO.println s!"{last2}"                          -- [1, 2, 30, 40]
```

### Nested Traversals

Compose traversals to reach into nested collections:

```lean
-- Given our Company/Department/Employee structures from before
def allEmployees : Traversal' Company Employee :=
  departmentsTraversal ⊚ employeesTraversal

def allSalaries : Traversal' Company Int :=
  allEmployees ⊚ salaryLens

def example4d (company : Company) : IO Unit := do
  -- Give everyone a 10% raise
  let updated := over allSalaries (fun s => s + s / 10) company

  -- Find all employees earning > 100k
  let highEarners := Fold.toList (allEmployees ⊚ filtered (·.salary > 100000)) company

  -- Count total employees
  IO.println s!"Total employees: {lengthOf allEmployees company}"
```

### Effectful Traversal

Traverse with effects (IO, State, etc.):

```lean
def example4e : IO Unit := do
  let nums := [1, 2, 3]

  -- Print each number while collecting results
  let result ← Traversal.traverse' traversed
    (fun n => do IO.println s!"Processing {n}"; pure (n * 2))
    nums
  IO.println s!"Result: {result}"
  -- Output:
  -- Processing 1
  -- Processing 2
  -- Processing 3
  -- Result: [2, 4, 6]
```

---

## 5. Real-World Patterns

### Pattern: Deep Nested Updates

Update deeply nested data without boilerplate:

```lean
structure AppState where
  user : Option User
  settings : Settings
  cache : Cache

structure User where
  profile : Profile
  preferences : Preferences

structure Profile where
  name : String
  avatar : Option String

-- Compose path to deeply nested field
def userAvatarPath : AffineTraversal' AppState String :=
  userLens ⊚ somePrism' ⊚ profileLens ⊚ avatarLens ⊚ somePrism'

-- Update avatar if user exists and has one
def updateAvatar (newUrl : String) (state : AppState) : AppState :=
  set userAvatarPath newUrl state
```

### Pattern: Batch Updates

Apply the same transformation to many fields:

```lean
-- Sanitize all string fields in a form
def sanitizeForm (form : FormData) : FormData :=
  form
    & nameLens %~ String.trim
    & emailLens %~ String.trim
    & addressLens ⊚ streetLens %~ String.trim
    & addressLens ⊚ cityLens %~ String.trim
```

### Pattern: Conditional Updates

Update only when conditions are met:

```lean
-- Give raises only to employees in a specific department
def giveRaises (deptName : String) (amount : Int) : Company → Company :=
  over (departmentsTraversal
        ⊚ filtered (·.name == deptName)
        ⊚ employeesTraversal
        ⊚ salaryLens)
       (· + amount)
```

### Pattern: Validation with Prisms

Use prisms to validate and transform data:

```lean
-- Prism for valid email (simplified)
def emailPrism : Prism' String String :=
  prismFromPartial
    (fun s => if s.containsSubstr "@" then some s else none)
    id

-- Prism for age in valid range
def validAgePrism : Prism' Int Int :=
  prismFromPartial
    (fun n => if 0 ≤ n && n ≤ 150 then some n else none)
    id

-- Validate form fields
def validateUser (input : RawUserInput) : Option ValidUser :=
  match input.email ^? emailPrism, input.age ^? validAgePrism with
  | some email, some age => some { email, age, name := input.name }
  | _, _ => none
```

### Pattern: JSON-like Navigation

Navigate dynamic or semi-structured data:

```lean
inductive JsonValue where
  | null
  | bool (b : Bool)
  | number (n : Float)
  | string (s : String)
  | array (items : List JsonValue)
  | object (fields : List (String × JsonValue))

-- Prism for each variant
def jsonString : Prism' JsonValue String := ...
def jsonArray : Prism' JsonValue (List JsonValue) := ...
def jsonObject : Prism' JsonValue (List (String × JsonValue)) := ...

-- Access field by key
def field (key : String) : AffineTraversal' JsonValue JsonValue := ...

-- Navigate: obj.users[0].name
def firstUserName : AffineTraversal' JsonValue String :=
  field "users" ⊚ jsonArray ⊚ _head ⊚ field "name" ⊚ jsonString
```

---

## Summary

| Optic | Focus | Use Case |
|-------|-------|----------|
| **Lens** | Exactly 1 | Struct fields |
| **Prism** | 0 or 1 | Option, Sum types, validation |
| **Traversal** | 0 or more | Collections, filtered elements |
| **AffineTraversal** | 0 or 1 | Lens + Prism composition |
| **Iso** | Exactly 1, bidirectional | Type conversions |
| **Fold** | 0 or more (read-only) | Collecting data |
| **Setter** | 0 or more (write-only) | Bulk modifications |

### Key Operations

| Operation | Lens | Prism | Traversal |
|-----------|------|-------|-----------|
| `view` | Yes | No | No |
| `preview` | Yes* | Yes | No |
| `set` | Yes | Yes | Yes |
| `over` | Yes | Yes | Yes |
| `review` | No | Yes | No |
| `traverse` | Yes | Yes | Yes |
| `toList` | Yes | Yes | Yes |

*Lens preview always returns `some`

### Next Steps

- Explore the [examples/](../examples/) directory for complete working code
- Read the [cheatsheet](./cheatsheet.md) for quick reference
- Check out the API documentation for advanced features
