# Performance Guide

This guide covers performance characteristics of Collimator optics and when to use them effectively.

## When to Use Optics

### Use Optics When:

1. **Deep nesting**: Updating values 3+ levels deep
   ```lean
   -- Optic approach: clear, composable
   over (company ⊚ departments ⊚ employees ⊚ salary) (* 1.1) c

   -- Manual approach: verbose, error-prone
   { c with departments := c.departments.map fun d =>
       { d with employees := d.employees.map fun e =>
           { e with salary := e.salary * 1.1 } } }
   ```

2. **Optional data**: Navigating through Option, Sum, or custom ADTs
   ```lean
   -- Optic: handles missing gracefully
   preview (config ⊚ database ⊚ somePrism' ⊚ port) cfg

   -- Manual: nested pattern matching
   match cfg.config with
   | none => none
   | some c => match c.database with ...
   ```

3. **Collections**: Modifying elements matching criteria
   ```lean
   -- Optic: declarative
   over (users ⊚ traversed ⊚ filtered (·.active)) updateUser data
   ```

4. **Reusable access patterns**: When the same path is used repeatedly
   ```lean
   -- Define once, use everywhere
   def userEmail := user ⊚ contact ⊚ email
   ```

### Use Direct Code When:

1. **Single-level access**: Simple field access is faster
   ```lean
   -- Direct is clearer and faster
   point.x + 1

   -- Optic overhead not justified
   view xLens point + 1
   ```

2. **Performance-critical inner loops**: Optics add indirection
   ```lean
   -- For tight loops, consider direct access
   for p in points do
     result := result + p.x * p.y
   ```

3. **Simple transformations**: When the structure is obvious
   ```lean
   -- Direct is fine
   { person with age := person.age + 1 }
   ```

## Performance Characteristics

### Optic Composition

Optic composition (`⊚`) creates a new optic at each step:

```lean
-- Each ⊚ creates an intermediate optic
a ⊚ b ⊚ c ⊚ d
```

**Tip**: For frequently-used compositions, define them once:

```lean
-- Bad: recomputes composition each use
def updateSalary (f : Int → Int) (c : Company) :=
  over (companyLens ⊚ deptTraversal ⊚ empTraversal ⊚ salaryLens) f c

-- Better: define composition once
def allSalaries := companyLens ⊚ deptTraversal ⊚ empTraversal ⊚ salaryLens

def updateSalary (f : Int → Int) (c : Company) :=
  over allSalaries f c
```

### Traversal vs Manual Recursion

Traversals use `Applicative` abstraction, which has overhead:

```lean
-- Traversal approach
over traversed process items

-- Direct recursion (potentially faster for simple cases)
items.map process
```

For `List.map`-equivalent operations, direct recursion is often faster.
Use traversals when you need:
- Composition with other optics
- Effectful traversal (with `StateM`, `IO`, etc.)
- Uniform treatment of different container types

### Fold vs Direct Iteration

Folds also use abstraction that may add overhead:

```lean
-- Fold approach
lengthOf traversed items
sumOf traversed numbers

-- Direct (faster for simple aggregations)
items.length
numbers.foldl (· + ·) 0
```

Use folds when:
- The aggregation is part of a larger optic composition
- You need to traverse through nested structures
- Uniformity across container types is valuable

## Inlining

Most Collimator optics are marked `@[inline]`, which helps the compiler optimize away abstraction overhead. For performance-critical code:

1. **Check inlining**: Ensure your composed optics can be inlined
2. **Use concrete types**: Avoid excessive polymorphism in hot paths
3. **Profile first**: Measure before optimizing

## Memory Allocation

### Lens Updates

`set` and `over` create new structures (Lean uses persistent data structures):

```lean
-- Creates new Point, doesn't mutate original
set xLens 10 point
```

For large structures with frequent updates, consider:
- Using `StateM` with mutable references
- Batching updates before applying

### Traversal Allocations

`toListOf` and similar operations allocate intermediate lists:

```lean
-- Allocates list of all foci
let items := toListOf traversed structure
```

For large collections, consider streaming alternatives when available.

## Benchmarking Tips

1. **Use realistic data**: Benchmark with production-sized structures
2. **Measure end-to-end**: Include the full operation, not just the optic
3. **Consider alternatives**: Compare optic vs direct implementation
4. **Profile memory**: Check allocation patterns, not just time

## Summary

| Scenario | Recommendation |
|----------|----------------|
| Deep nesting (3+ levels) | Use optics |
| Optional/sum types | Use optics (prisms) |
| Collection traversal | Use optics for composition, direct for simple maps |
| Single-field access | Direct access |
| Performance-critical loops | Direct access, profile |
| Reusable patterns | Define optic once, reuse |
| Effectful operations | Optics with Star |

The general principle: **optics excel at managing complexity**, trading some runtime overhead for clearer, more composable code. For simple operations, direct code is fine.
