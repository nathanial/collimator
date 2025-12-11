import Batteries
import Collimator.Combinators
import Collimator.Operators
import Collimator.Instances
import Collimator.Optics
import Collimator.Concrete.FunArrow
import CollimatorTests.Framework

namespace CollimatorTests.Combinators

open Batteries
open Collimator
open Collimator.Combinators
open Collimator.Indexed
open Collimator.Operators
open CollimatorTests

open scoped Collimator.Operators

testSuite "Combinators"

structure Player where
  name : String
  score : Int
  deriving BEq, Repr

private def scoreLens : Lens' Player Int :=
  lens' (fun p => p.score) (fun p s => { p with score := s })

test "operator syntax view/over/set works for lenses" := do
  let p : Player := { name := "Ada", score := 10 }
  ensureEq "view" 10 (p ^. scoreLens)
  let updated := p & scoreLens %~ (· + 5)
  ensureEq "over" 15 (updated ^. scoreLens)
  let reset := p & scoreLens .~ 0
  ensureEq "set" 0 (reset ^. scoreLens)

test "product instances supply convenient lenses" := do
  let pair := (3, true)
  let firstLens : Lens' (Int × Bool) Int :=
    Collimator.Instances.Prod.first (α := Int) (β := Bool) (γ := Int)
  let secondLens : Lens' (Int × Bool) Bool :=
    Collimator.Instances.Prod.second (α := Int) (β := Bool) (γ := Bool)
  let bumpedFirst := pair & firstLens %~ (· + 1)
  ensureEq "bump first" (4, true) bumpedFirst
  let toggled := pair & secondLens %~ not
  ensureEq "toggle second" (3, false) toggled
  let triple : (Int × Int) × Int := ((1, 2), 3)
  let lens : Lens' ((Int × Int) × Int) Int :=
    Collimator.Instances.Prod.firstOfTriple (α := Int) (β := Int) (γ := Int) (δ := Int)
  let incremented := triple & lens %~ (· + 10)
  ensureEq "first of triple" ((11, 2), 3) incremented

test "sum prisms preview and review branches" := do
  let leftPrism : Prism (Sum Int String) (Sum Int String) Int Int :=
    Collimator.Instances.Sum.left
      (α := Int) (β := String) (γ := Int)
  let inLeft : Sum Int String := Sum.inl (7 : Int)
  let inRight : Sum Int String := Sum.inr (α := Int) ("optics" : String)
  ensureEq "preview left" (some (7 : Int)) (inLeft ^? leftPrism)
  ensureEq "preview right" (none : Option Int) (inRight ^? leftPrism)
  let expectedReview : Sum Int String := Sum.inl (5 : Int)
  ensureEq "review" expectedReview (review' leftPrism (5 : Int))

test "option prisms distinguish some and none" := do
  let somePrism : Prism (Option Int) (Option Int) Int Int :=
    Collimator.Instances.Option.somePrism (α := Int) (β := Int)
  ensureEq "preview some" (some 9) ((some 9) ^? somePrism)
  ensureEq "preview none" (none : Option Int) (none ^? somePrism)
  ensureEq "review some" (some 4) (review' somePrism 4)

test "list ix updates element at index" := do
  let elements := [10, 20, 30]
  let traversal : Traversal' (List Int) Int :=
    ix (ι := Nat) (s := List Int) (a := Int) 1
  let updated := elements & traversal %~ (· + 7)
  ensureEq "ix modifies" [10, 27, 30] updated

test "list at lens views optional element" := do
  let xs := ["lean", "optic", "library"]
  let l : Lens' (List String) (Option String) :=
    atLens (ι := Nat) (s := List String) (a := String) 2
  ensureEq "get existing" (some "library") (xs ^. l)
  ensureEq "missing" (none : Option String) (["lean"] ^. l)

test "array ix modifies in-bounds value and ignores out-of-bounds" := do
  let arr : Array Int := #[1, 2, 3]
  let traversal : Traversal' (Array Int) Int :=
    ix (ι := Nat) (s := Array Int) (a := Int) 0
  let updated := arr & traversal %~ (· * 2)
  ensureEq "modify first" #[2, 2, 3] updated
  let untouched := arr & (ix (ι := Nat) (s := Array Int) (a := Int) 5) %~ (· + 1)
  ensureEq "oob" #[1, 2, 3] untouched

test "filtered traversal only updates predicate matches" := do
  let tr : Traversal' (List Int) Int :=
    Collimator.Instances.List.traversed (α := Int) (β := Int)
  let evens : Traversal' (List Int) Int :=
    filtered tr (fun n => n % 2 == 0)
  let result := [1, 2, 3, 4] & evens %~ (· + 1)
  ensureEq "filtered update" [1, 3, 3, 5] result

test "itraversed exposes index during updates" := do
  let base : Traversal' (List Int) (Nat × Int) :=
    Collimator.Instances.List.itraversed
  let bumped := [5, 5, 5] & base %~ (fun | (idx, v) => (idx, v + idx))
  ensureEq "index applied" [5, 6, 7] bumped

#generate_tests

end CollimatorTests.Combinators
