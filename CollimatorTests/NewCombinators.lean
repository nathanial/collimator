import CollimatorTests.Framework
import Collimator.Prelude
import Collimator.Helpers

/-!
# Tests for New Combinators

Tests for the combinators added in the improvements:
- filteredList, ifilteredList
- _head, _last, taking, dropping
- anyOf, allOf, findOf, lengthOf, sumOf, nullOf
- failing, prismFromPartial
- orElse
-/

open CollimatorTests
open Collimator
open Collimator.Poly
open Collimator.Combinators
open Collimator.Instances.List
open Collimator.Instances.Option
open scoped Collimator.Operators

namespace CollimatorTests.NewCombinators

/-! ## filteredList Tests -/

def filteredListTests : List TestCase := [
  { name := "filteredList: double only positive numbers"
    run := do
      let result := Traversal.over' (filteredList (· > 0)) (· * 2) [-1, 2, -3, 4]
      ensureEq "positive doubled" [-1, 4, -3, 8] result
  },
  { name := "filteredList: filter none"
    run := do
      let result := Traversal.over' (filteredList (· > 100)) (· * 2) [1, 2, 3]
      ensureEq "none match" [1, 2, 3] result
  },
  { name := "filteredList: filter all"
    run := do
      let result := Traversal.over' (filteredList (· > 0)) (· * 2) [1, 2, 3]
      ensureEq "all match" [2, 4, 6] result
  },
  { name := "filteredList: collect filtered elements"
    run := do
      let result := Fold.toListTraversal (filteredList (· > 0)) [-1, 2, -3, 4]
      ensureEq "collect positives" [2, 4] result
  },
  { name := "filteredList: empty list"
    run := do
      let result := Traversal.over' (filteredList (· > 0)) (· * 2) ([] : List Int)
      ensureEq "empty list unchanged" [] result
  }
]

def ifilteredListTests : List TestCase := [
  { name := "ifilteredList: modify even indices"
    run := do
      let result := Traversal.over' (ifilteredList (fun i _ => i % 2 == 0)) String.toUpper ["a", "b", "c", "d"]
      ensureEq "even indices uppercase" ["A", "b", "C", "d"] result
  },
  { name := "ifilteredList: filter by index and value"
    run := do
      let result := Fold.toListTraversal (ifilteredList (fun i x => i < 2 && x > 0)) [-1, 2, 3, -4]
      ensureEq "index < 2 and value > 0" [2] result
  }
]

/-! ## List Operations Tests -/

def headTests : List TestCase := [
  { name := "_head: preview non-empty"
    run := do
      let result := AffineTraversalOps.preview' _head [1, 2, 3]
      ensureEq "head is 1" (some 1) result
  },
  { name := "_head: preview empty"
    run := do
      let result := AffineTraversalOps.preview' _head ([] : List Int)
      ensureEq "head is none" (none : Option Int) result
  },
  { name := "_head: over non-empty"
    run := do
      let result := AffineTraversalOps.over _head (· * 10) [1, 2, 3]
      ensureEq "head modified" [10, 2, 3] result
  },
  { name := "_head: over empty"
    run := do
      let result := AffineTraversalOps.over _head (· * 10) ([] : List Int)
      ensureEq "empty unchanged" [] result
  },
  { name := "_head: set value"
    run := do
      let result := AffineTraversalOps.set _head 100 [1, 2, 3]
      ensureEq "head set" [100, 2, 3] result
  }
]

def lastTests : List TestCase := [
  { name := "_last: preview non-empty"
    run := do
      let result := AffineTraversalOps.preview' _last [1, 2, 3]
      ensureEq "last is 3" (some 3) result
  },
  { name := "_last: preview singleton"
    run := do
      let result := AffineTraversalOps.preview' _last [42]
      ensureEq "single element" (some 42) result
  },
  { name := "_last: preview empty"
    run := do
      let result := AffineTraversalOps.preview' _last ([] : List Int)
      ensureEq "last is none" (none : Option Int) result
  },
  { name := "_last: over non-empty"
    run := do
      let result := AffineTraversalOps.over _last (· * 10) [1, 2, 3]
      ensureEq "last modified" [1, 2, 30] result
  }
]

def takingTests : List TestCase := [
  { name := "taking: first 2 elements"
    run := do
      let result := Traversal.over' (taking 2) (· * 10) [1, 2, 3, 4]
      ensureEq "first 2 modified" [10, 20, 3, 4] result
  },
  { name := "taking: take 0"
    run := do
      let result := Traversal.over' (taking 0) (· * 10) [1, 2, 3]
      ensureEq "none modified" [1, 2, 3] result
  },
  { name := "taking: take more than length"
    run := do
      let result := Traversal.over' (taking 10) (· * 10) [1, 2]
      ensureEq "all modified" [10, 20] result
  },
  { name := "taking: collect"
    run := do
      let result := Fold.toListTraversal (taking 2) [1, 2, 3, 4, 5]
      ensureEq "first 2 collected" [1, 2] result
  }
]

def droppingTests : List TestCase := [
  { name := "dropping: skip first 2"
    run := do
      let result := Traversal.over' (dropping 2) (· * 10) [1, 2, 3, 4]
      ensureEq "last 2 modified" [1, 2, 30, 40] result
  },
  { name := "dropping: skip 0"
    run := do
      let result := Traversal.over' (dropping 0) (· * 10) [1, 2, 3]
      ensureEq "all modified" [10, 20, 30] result
  },
  { name := "dropping: skip more than length"
    run := do
      let result := Traversal.over' (dropping 10) (· * 10) [1, 2]
      ensureEq "none modified" [1, 2] result
  },
  { name := "dropping: collect"
    run := do
      let result := Fold.toListTraversal (dropping 2) [1, 2, 3, 4, 5]
      ensureEq "last 3 collected" [3, 4, 5] result
  }
]

/-! ## Fold Enhancement Tests with Traversals -/

def foldEnhancementTests : List TestCase := [
  { name := "toListTraversal: basic"
    run := do
      let result := Fold.toListTraversal traversed [1, 2, 3]
      ensureEq "collect all" [1, 2, 3] result
  },
  { name := "toListTraversal: empty"
    run := do
      let result := Fold.toListTraversal traversed ([] : List Int)
      ensureEq "empty list" [] result
  }
]

/-! ## Prism Utility Tests -/

def prismUtilityTests : List TestCase := [
  { name := "failing: preview always none"
    run := do
      let result := preview' (failing : Prism' Int String) 42
      ensureEq "always fails" none result
  },
  { name := "failing: over is identity"
    run := do
      let failingPrism : Prism' Int Int := failing
      let result := AffineTraversalOps.over (AffineTraversalOps.ofPrism failingPrism) (· * 2) 42
      ensureEq "unchanged" 42 result
  },
  { name := "prismFromPartial: even numbers"
    run := do
      let evenPrism : Prism' Int Int := prismFromPartial
        (fun n : Int => if n % 2 == 0 then some n else none)
        _root_.id
      ensureEq "4 is even" (some 4) (preview' evenPrism 4)
      ensureEq "5 is odd" none (preview' evenPrism 5)
  },
  { name := "prismFromPartial: review"
    run := do
      let evenPrism : Prism' Int Int := prismFromPartial
        (fun n : Int => if n % 2 == 0 then some n else none)
        _root_.id
      ensureEq "review returns value" 10 (review' evenPrism 10)
  }
]

/-! ## orElse Tests -/

def orElseTests : List TestCase := [
  { name := "orElse: first matches"
    run := do
      let p1 : Prism' Int Int := prismFromPartial (fun n : Int => if n > 0 then some n else none) _root_.id
      let p2 : Prism' Int Int := prismFromPartial (fun n : Int => if n < 0 then some n else none) _root_.id
      let combined : AffineTraversal' Int Int := orElse p1 p2
      ensureEq "positive wins" (some 5) (AffineTraversalOps.preview' combined 5)
  },
  { name := "orElse: second matches"
    run := do
      let p1 : Prism' Int Int := prismFromPartial (fun n : Int => if n > 0 then some n else none) _root_.id
      let p2 : Prism' Int Int := prismFromPartial (fun n : Int => if n < 0 then some n else none) _root_.id
      let combined : AffineTraversal' Int Int := orElse p1 p2
      ensureEq "negative wins" (some (-3)) (AffineTraversalOps.preview' combined (-3))
  },
  { name := "orElse: neither matches"
    run := do
      let p1 : Prism' Int Int := prismFromPartial (fun n : Int => if n > 10 then some n else none) _root_.id
      let p2 : Prism' Int Int := prismFromPartial (fun n : Int => if n < -10 then some n else none) _root_.id
      let combined : AffineTraversal' Int Int := orElse p1 p2
      ensureEq "zero fails both" (none : Option Int) (AffineTraversalOps.preview' combined 0)
  }
]

/-! ## Monomorphic Operator Tests -/

def monomorphicOpTests : List TestCase := [
  { name := "^.' operator: view"
    run := do
      let pair := (10, "hello")
      let lens : Lens' (Int × String) Int := _1
      let result := pair ^.' lens
      ensureEq "view first" 10 result
  },
  { name := ".~' operator: set"
    run := do
      let pair := (10, "hello")
      let lens : Lens' (Int × String) Int := _1
      let setter := lens .~' 99
      let result := setter pair
      ensureEq "set first" (99, "hello") result
  },
  { name := "%~' operator: over"
    run := do
      let pair := (10, "hello")
      let lens : Lens' (Int × String) Int := _1
      let modifier := lens %~' (· * 2)
      let result := modifier pair
      ensureEq "double first" (20, "hello") result
  },
  { name := "^?' operator: preview some"
    run := do
      let opt : Option Int := some 42
      let result := opt ^?' (somePrism' Int)
      ensureEq "preview some" (some 42) result
  },
  { name := "^?' operator: preview none"
    run := do
      let opt : Option Int := none
      let result := opt ^?' (somePrism' Int)
      ensureEq "preview none" none result
  }
]

/-! ## Helper Tests -/

private structure TestPoint where
  x : Int
  y : Int
  deriving BEq, Repr

def helperTests : List TestCase := [
  { name := "first': explicit tuple lens"
    run := do
      let pair := (10, "hello")
      let fstLens : Lens' (Int × String) Int := Helpers.first' Int String
      let result := view' fstLens pair
      ensureEq "view first" 10 result
  },
  { name := "second': explicit tuple lens"
    run := do
      let pair := (10, "hello")
      let sndLens : Lens' (Int × String) String := Helpers.second' Int String
      let result := view' sndLens pair
      ensureEq "view second" "hello" result
  },
  { name := "some': explicit option prism"
    run := do
      let opt : Option Int := some 42
      let somePrism : Prism' (Option Int) Int := Helpers.some' Int
      let result := preview' somePrism opt
      ensureEq "preview some" (some 42) result
  },
  { name := "each': explicit list traversal"
    run := do
      let lst := [1, 2, 3]
      let result := Fold.toListTraversal (Helpers.each' Int) lst
      ensureEq "collect all" [1, 2, 3] result
  },
  { name := "lensOf: build lens with explicit types"
    run := do
      let xLens : Lens' TestPoint Int := Helpers.lensOf TestPoint Int (·.x) (fun p x => { p with x := x })
      let p := TestPoint.mk 10 20
      ensureEq "view x" 10 (view' xLens p)
      ensureEq "set x" (TestPoint.mk 99 20) (set' xLens 99 p)
  },
  { name := "prismOf: build prism with explicit types"
    run := do
      let positivePrism : Prism' Int Int := Helpers.prismOf Int Int _root_.id (fun n => if n > 0 then some n else none)
      ensureEq "positive matches" (some 5) (preview' positivePrism 5)
      ensureEq "negative fails" (none : Option Int) (preview' positivePrism (-3))
  }
]

/-! ## All Cases -/

def cases : List TestCase :=
  filteredListTests ++
  ifilteredListTests ++
  headTests ++
  lastTests ++
  takingTests ++
  droppingTests ++
  foldEnhancementTests ++
  prismUtilityTests ++
  orElseTests ++
  monomorphicOpTests ++
  helperTests

end CollimatorTests.NewCombinators
