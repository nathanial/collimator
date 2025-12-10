import Batteries
import Collimator.Core.Profunctor
import Collimator.Core.Strong
import Collimator.Core.Choice
import Collimator.Core.Laws
import CollimatorTests.Framework

namespace CollimatorTests.Core

open Batteries
open Collimator.Core
open CollimatorTests

private def case_dimapArrow : TestCase := {
  name := "profunctor arrow dimap applies pre- and post-maps",
  run := do
    let p : Nat → String := fun n => s!"n={n}"
    let transformed := Profunctor.dimap (P := fun α β : Type => α → β)
      (fun n => n + 2) (fun s => s ++ "!") p
    let actual := transformed 3
    ensureEq "dimap arrow" "n=5!" actual
}

private def case_lmapRmap : TestCase := {
  name := "lmap and rmap specialize dimap",
  run := do
    let p : Nat → Nat := fun n => n * 2
    let leftMapped := lmap (P := fun α β : Type => α → β) (fun n => n + 1) p
    let rightMapped := rmap (P := fun α β : Type => α → β) (fun n => n + 3) p
    ensureEq "lmap applies pre-map" 8 (leftMapped 3)
    ensureEq "rmap applies post-map" 9 (rightMapped 3)
}

private def case_strongArrow : TestCase := {
  name := "strong arrow distributes over products",
  run := do
    let p : Nat → Nat := fun n => n + 1
    let firstF := Strong.first (P := fun α β : Type => α → β) p
    let secondF := Strong.second (P := fun α β : Type => α → β) p
    ensureEq "first keeps context" (7, "ctx") (firstF (6, "ctx"))
    ensureEq "second keeps context" ("ctx", 11) (secondF ("ctx", 10))
}

private def case_choiceArrow : TestCase := {
  name := "choice arrow distributes over sums",
  run := do
    let p : Nat → Bool := fun n => n % 2 == 0
    let leftF := Choice.left (P := fun α β : Type => α → β) p
    let rightF := Choice.right (P := fun α β : Type => α → β) p
    match leftF (Sum.inl 4) with
    | Sum.inl b => ensure (b) "left maps Sum.inl"
    | _ => ensure false "left should map Sum.inl to Sum.inl"
    match leftF (Sum.inr "tag") with
    | Sum.inr tag => ensure (tag == "tag") "left preserves Sum.inr"
    | _ => ensure false "left should preserve Sum.inr"
    match rightF (Sum.inr 5) with
    | Sum.inr b => ensure (b == false) "right maps Sum.inr"
    | _ => ensure false "right should map Sum.inr to Sum.inr"
    match rightF (Sum.inl "orig") with
    | Sum.inl tag => ensure (tag == "orig") "right preserves Sum.inl"
    | _ => ensure false "right should preserve Sum.inl"
}

private def case_constDimap : TestCase := {
  name := "const profunctor ignores morphisms",
  run := do
    let payload : Const String Nat Nat := "payload"
    let remapped := Profunctor.dimap (P := Const String) (fun | n => n + 1)
      (fun | s => s ++ "!") payload
    ensureEq "const untouched" "payload" remapped
}

private def case_kleisliDimap : TestCase := {
  name := "kleisli dimap composes with Functor.map",
  run := do
    let p : Kleisli Option Nat String := fun n =>
      if n % 2 == 0 then some (s!"{n}") else none
    let remapped := Profunctor.dimap (P := Kleisli Option)
      (fun n => n + 1) (fun s => s ++ "!") p
    ensureEq "kleisli maps some" (some "4!") (remapped 3)
    ensureEq "kleisli maps none" (none : Option String) (remapped 2)
}

private def case_dimapCompLaw : TestCase := {
  name := "lawful arrow dimap composition matches sequential dimaps",
  run := do
    let p : Nat → String := fun n => s!"{n}"
    let f : Nat → Nat := fun n => n + 1
    let f' : Nat → Nat := fun n => n * 2
    let g : String → String := fun s => s ++ "?"
    let g' : String → Nat := fun s => s.length
    let lhs := Profunctor.dimap (P := fun α β : Type => α → β)
      (f ∘ f') (g' ∘ g) p
    let rhs :=
      Profunctor.dimap (P := fun α β : Type => α → β) f' g'
        (Profunctor.dimap (P := fun α β : Type => α → β) f g p)
    ensureEq "dimap composition" (lhs 3) (rhs 3)
    ensureEq "dimap composition'" (lhs 5) (rhs 5)
}

/--
All profunctor core test cases.
-/
def cases : List TestCase :=
  [ case_dimapArrow
  , case_lmapRmap
  , case_strongArrow
  , case_choiceArrow
  , case_constDimap
  , case_kleisliDimap
  , case_dimapCompLaw
  ]

end CollimatorTests.Core
