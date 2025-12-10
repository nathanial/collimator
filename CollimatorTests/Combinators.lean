import Batteries
import Collimator.Combinators
import Collimator.Operators
import Collimator.Instances.Prod
import Collimator.Instances.Sum
import Collimator.Instances.Option
import Collimator.Instances.List
import Collimator.Instances.Array
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

structure Player where
  name : String
  score : Int
  deriving BEq, Repr

private def scoreLens : Lens' Player Int :=
  lens' (fun p => p.score) (fun p s => { p with score := s })

private def case_operatorSyntax : TestCase := {
  name := "operator syntax view/over/set works for lenses",
  run := do
    let p : Player := { name := "Ada", score := 10 }
    ensureEq "view" 10 (Collimator.view' scoreLens p)
    let setter : Setter Player Player Int Int := scoreLens
    let updated := Setter.over' setter (fun n => n + 5) p
    ensureEq "over" 15 (Collimator.view' scoreLens updated)
    let reset := Setter.set' setter 0 p
    ensureEq "set" 0 (Collimator.view' scoreLens reset)
}

private def case_prodInstances : TestCase := {
  name := "product instances supply convenient lenses",
  run := do
    let pair := (3, true)
    let firstLens : Setter (Int × Bool) (Int × Bool) Int Int :=
      Collimator.Instances.Prod.first (α := Int) (β := Bool) (γ := Int)
    let secondLens : Setter (Int × Bool) (Int × Bool) Bool Bool :=
      Collimator.Instances.Prod.second (α := Int) (β := Bool) (γ := Bool)
    let bumpedFirst := Setter.over' firstLens (fun n => n + 1) pair
    ensureEq "bump first" (4, true) bumpedFirst
    let toggled := Setter.over' secondLens not pair
    ensureEq "toggle second" (3, false) toggled
    let triple : (Int × Int) × Int := ((1, 2), 3)
    let lens : Setter ((Int × Int) × Int) ((Int × Int) × Int) Int Int :=
      Collimator.Instances.Prod.firstOfTriple (α := Int) (β := Int) (γ := Int) (δ := Int)
    let incremented := Setter.over' lens (fun n => n + 10) triple
    ensureEq "first of triple" ((11, 2), 3) incremented
}

private def case_sumPrisms : TestCase := {
  name := "sum prisms preview and review branches",
  run := do
    let leftPrism : Prism (Sum Int String) (Sum Int String) Int Int :=
      Collimator.Instances.Sum.left
        (α := Int) (β := String) (γ := Int)
    let inLeft : Sum Int String := Sum.inl (7 : Int)
    let inRight : Sum Int String := Sum.inr (α := Int) ("optics" : String)
    ensureEq "preview left" (some (7 : Int)) (preview' leftPrism inLeft)
    ensureEq "preview right" (none : Option Int) (preview' leftPrism inRight)
    let expectedReview : Sum Int String := Sum.inl (5 : Int)
    ensureEq "review" expectedReview (review' leftPrism (5 : Int))
}

private def case_optionPrisms : TestCase := {
  name := "option prisms distinguish some and none",
  run := do
    let somePrism : Prism (Option Int) (Option Int) Int Int :=
      Collimator.Instances.Option.somePrism (α := Int) (β := Int)
    ensureEq "preview some" (some 9) (preview' somePrism (some 9))
    ensureEq "preview none" (none : Option Int) (preview' somePrism none)
    ensureEq "review some" (some 4) (review' somePrism 4)
}

private def case_listIx : TestCase := {
  name := "list ix updates element at index",
  run := do
    let elements := [10, 20, 30]
    let traversal : Traversal' (List Int) Int :=
      ix (ι := Nat) (s := List Int) (a := Int) 1
    let updated := Traversal.over' traversal (fun n => n + 7) elements
    ensureEq "ix modifies" [10, 27, 30] updated
}

private def case_listAt : TestCase := {
  name := "list at lens views optional element",
  run := do
    let xs := ["lean", "optic", "library"]
    let l : Lens' (List String) (Option String) :=
      atLens (ι := Nat) (s := List String) (a := String) 2
    ensureEq "get existing" (some "library") (view' l xs)
    ensureEq "missing" (none : Option String) (view' l ["lean"])
}

private def case_arrayIx : TestCase := {
  name := "array ix modifies in-bounds value and ignores out-of-bounds",
  run := do
    let arr : Array Int := #[1, 2, 3]
    let traversal : Traversal' (Array Int) Int :=
      ix (ι := Nat) (s := Array Int) (a := Int) 0
    let updated := Traversal.over' traversal (fun n => n * 2) arr
    ensureEq "modify first" #[2, 2, 3] updated
    let untouched :=
      Traversal.over' (ix (ι := Nat) (s := Array Int) (a := Int) 5) (fun n => n + 1) arr
    ensureEq "oob" #[1, 2, 3] untouched
}

private def case_filteredTraversal : TestCase := {
  name := "filtered traversal only updates predicate matches",
  run := do
    let tr : Traversal' (List Int) Int :=
      Collimator.Instances.List.traversed (α := Int) (β := Int)
    let evens : Traversal' (List Int) Int :=
      filtered tr (fun n => n % 2 == 0)
    let result := Traversal.over' evens (fun n => n + 1) [1, 2, 3, 4]
    ensureEq "filtered update" [1, 3, 3, 5] result
}

private def case_itraversedUsesIndex : TestCase := {
  name := "itraversed exposes index during updates",
  run := do
    let base : Traversal' (List Int) (Nat × Int) :=
      Collimator.Instances.List.itraversed
    let bumped := Traversal.over' base (fun | (idx, v) => (idx, v + idx)) [5, 5, 5]
    ensureEq "index applied" [5, 6, 7] bumped
}

/--
All combinators optic test cases.
-/
def cases : List TestCase :=
  [ case_operatorSyntax
  , case_prodInstances
  , case_sumPrisms
  , case_optionPrisms
  , case_listIx
  , case_listAt
  , case_arrayIx
  , case_filteredTraversal
  , case_itraversedUsesIndex
  ]

end CollimatorTests.Combinators
