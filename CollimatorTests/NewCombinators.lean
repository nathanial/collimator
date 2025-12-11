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
open Collimator.Combinators
open Collimator.Instances.List
open Collimator.Instances.Option
open scoped Collimator.Operators

namespace CollimatorTests.NewCombinators

testSuite "New Combinators"

/-! ## filteredList Tests -/

test "filteredList: double only positive numbers" := do
  let result := [-1, 2, -3, 4] & filteredList (· > 0) %~ (· * 2)
  ensureEq "positive doubled" [-1, 4, -3, 8] result

test "filteredList: filter none" := do
  let result := [1, 2, 3] & filteredList (· > 100) %~ (· * 2)
  ensureEq "none match" [1, 2, 3] result

test "filteredList: filter all" := do
  let result := [1, 2, 3] & filteredList (· > 0) %~ (· * 2)
  ensureEq "all match" [2, 4, 6] result

test "filteredList: collect filtered elements" := do
  let result := [-1, 2, -3, 4] ^.. filteredList (· > 0)
  ensureEq "collect positives" [2, 4] result

test "filteredList: empty list" := do
  let result := ([] : List Int) & filteredList (· > 0) %~ (· * 2)
  ensureEq "empty list unchanged" [] result

test "ifilteredList: modify even indices" := do
  let result := ["a", "b", "c", "d"] & ifilteredList (fun i _ => i % 2 == 0) %~ String.toUpper
  ensureEq "even indices uppercase" ["A", "b", "C", "d"] result

test "ifilteredList: filter by index and value" := do
  let result := [-1, 2, 3, -4] ^.. ifilteredList (fun i x => i < 2 && x > 0)
  ensureEq "index < 2 and value > 0" [2] result

/-! ## List Operations Tests -/

test "_head: preview non-empty" := do
  let result := [1, 2, 3] ^? _head
  ensureEq "head is 1" (some 1) result

test "_head: preview empty" := do
  let result := ([] : List Int) ^? _head
  ensureEq "head is none" (none : Option Int) result

test "_head: over non-empty" := do
  let result := [1, 2, 3] & _head %~ (· * 10)
  ensureEq "head modified" [10, 2, 3] result

test "_head: over empty" := do
  let result := ([] : List Int) & _head %~ (· * 10)
  ensureEq "empty unchanged" [] result

test "_head: set value" := do
  let result := [1, 2, 3] & _head .~ 100
  ensureEq "head set" [100, 2, 3] result

test "_last: preview non-empty" := do
  let result := [1, 2, 3] ^? _last
  ensureEq "last is 3" (some 3) result

test "_last: preview singleton" := do
  let result := [42] ^? _last
  ensureEq "single element" (some 42) result

test "_last: preview empty" := do
  let result := ([] : List Int) ^? _last
  ensureEq "last is none" (none : Option Int) result

test "_last: over non-empty" := do
  let result := [1, 2, 3] & _last %~ (· * 10)
  ensureEq "last modified" [1, 2, 30] result

test "taking: first 2 elements" := do
  let result := [1, 2, 3, 4] & taking 2 %~ (· * 10)
  ensureEq "first 2 modified" [10, 20, 3, 4] result

test "taking: take 0" := do
  let result := [1, 2, 3] & taking 0 %~ (· * 10)
  ensureEq "none modified" [1, 2, 3] result

test "taking: take more than length" := do
  let result := [1, 2] & taking 10 %~ (· * 10)
  ensureEq "all modified" [10, 20] result

test "taking: collect" := do
  let result := [1, 2, 3, 4, 5] ^.. taking 2
  ensureEq "first 2 collected" [1, 2] result

test "dropping: skip first 2" := do
  let result := [1, 2, 3, 4] & dropping 2 %~ (· * 10)
  ensureEq "last 2 modified" [1, 2, 30, 40] result

test "dropping: skip 0" := do
  let result := [1, 2, 3] & dropping 0 %~ (· * 10)
  ensureEq "all modified" [10, 20, 30] result

test "dropping: skip more than length" := do
  let result := [1, 2] & dropping 10 %~ (· * 10)
  ensureEq "none modified" [1, 2] result

test "dropping: collect" := do
  let result := [1, 2, 3, 4, 5] ^.. dropping 2
  ensureEq "last 3 collected" [3, 4, 5] result

/-! ## Fold Enhancement Tests with Traversals -/

test "toListTraversal: basic" := do
  let result := [1, 2, 3] ^.. traversed
  ensureEq "collect all" [1, 2, 3] result

test "toListTraversal: empty" := do
  let result := ([] : List Int) ^.. traversed
  ensureEq "empty list" [] result

/-! ## Prism Utility Tests -/

test "failing: preview always none" := do
  let failingPrism : Prism' Int String := failing
  let result := (42 : Int) ^? failingPrism
  ensureEq "always fails" (none : Option String) result

test "failing: over is identity" := do
  let failingPrism : Prism' Int Int := failing
  let result := 42 & failingPrism %~ (· * 2)
  ensureEq "unchanged" 42 result

test "prismFromPartial: even numbers" := do
  let evenPrism : Prism' Int Int := prismFromPartial
    (fun n : Int => if n % 2 == 0 then some n else none)
    _root_.id
  ensureEq "4 is even" (some 4) (4 ^? evenPrism)
  ensureEq "5 is odd" none (5 ^? evenPrism)

test "prismFromPartial: review" := do
  let evenPrism : Prism' Int Int := prismFromPartial
    (fun n : Int => if n % 2 == 0 then some n else none)
    _root_.id
  ensureEq "review returns value" 10 (review' evenPrism 10)

/-! ## orElse Tests -/

test "orElse: first matches" := do
  let p1 : Prism' Int Int := prismFromPartial (fun n : Int => if n > 0 then some n else none) _root_.id
  let p2 : Prism' Int Int := prismFromPartial (fun n : Int => if n < 0 then some n else none) _root_.id
  let combined : AffineTraversal' Int Int := orElse p1 p2
  ensureEq "positive wins" (some 5) (5 ^? combined)

test "orElse: second matches" := do
  let p1 : Prism' Int Int := prismFromPartial (fun n : Int => if n > 0 then some n else none) _root_.id
  let p2 : Prism' Int Int := prismFromPartial (fun n : Int => if n < 0 then some n else none) _root_.id
  let combined : AffineTraversal' Int Int := orElse p1 p2
  ensureEq "negative wins" (some (-3)) ((-3) ^? combined)

test "orElse: neither matches" := do
  let p1 : Prism' Int Int := prismFromPartial (fun n : Int => if n > 10 then some n else none) _root_.id
  let p2 : Prism' Int Int := prismFromPartial (fun n : Int => if n < -10 then some n else none) _root_.id
  let combined : AffineTraversal' Int Int := orElse p1 p2
  ensureEq "zero fails both" (none : Option Int) (0 ^? combined)

/-! ## Monomorphic Operator Tests -/

test "^. operator: view" := do
  let pair := (10, "hello")
  let lens : Lens' (Int × String) Int := _1
  let result := pair ^. lens
  ensureEq "view first" 10 result

test ".~ operator: set" := do
  let pair := (10, "hello")
  let lens : Lens' (Int × String) Int := _1
  let setter := lens .~ 99
  let result := setter pair
  ensureEq "set first" (99, "hello") result

test "%~ operator: over" := do
  let pair := (10, "hello")
  let lens : Lens' (Int × String) Int := _1
  let modifier := lens %~ (· * 2)
  let result := modifier pair
  ensureEq "double first" (20, "hello") result

test "^? operator: preview some" := do
  let opt : Option Int := some 42
  let result := opt ^? (somePrism' Int)
  ensureEq "preview some" (some 42) result

test "^? operator: preview none" := do
  let opt : Option Int := none
  let result := opt ^? (somePrism' Int)
  ensureEq "preview none" none result

/-! ## Helper Tests -/

private structure TestPoint where
  x : Int
  y : Int
  deriving BEq, Repr

test "first': explicit tuple lens" := do
  let pair := (10, "hello")
  let fstLens : Lens' (Int × String) Int := Helpers.first' Int String
  let result := pair ^. fstLens
  ensureEq "view first" 10 result

test "second': explicit tuple lens" := do
  let pair := (10, "hello")
  let sndLens : Lens' (Int × String) String := Helpers.second' Int String
  let result := pair ^. sndLens
  ensureEq "view second" "hello" result

test "some': explicit option prism" := do
  let opt : Option Int := some 42
  let somePrism : Prism' (Option Int) Int := Helpers.some' Int
  let result := opt ^? somePrism
  ensureEq "preview some" (some 42) result

test "each': explicit list traversal" := do
  let lst := [1, 2, 3]
  let result := lst ^.. Helpers.each' Int
  ensureEq "collect all" [1, 2, 3] result

test "lensOf: build lens with explicit types" := do
  let xLens : Lens' TestPoint Int := Helpers.lensOf TestPoint Int (·.x) (fun p x => { p with x := x })
  let p := TestPoint.mk 10 20
  ensureEq "view x" 10 (p ^. xLens)
  ensureEq "set x" (TestPoint.mk 99 20) (p & xLens .~ 99)

test "prismOf: build prism with explicit types" := do
  let positivePrism : Prism' Int Int := Helpers.prismOf Int Int _root_.id (fun n => if n > 0 then some n else none)
  ensureEq "positive matches" (some 5) (5 ^? positivePrism)
  ensureEq "negative fails" (none : Option Int) ((-3) ^? positivePrism)

#generate_tests

end CollimatorTests.NewCombinators
