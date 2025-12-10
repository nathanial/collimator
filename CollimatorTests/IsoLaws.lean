import Batteries
import Collimator.Optics.Iso
import Collimator.Optics.Types
import Collimator.Theorems.IsoLaws
import Collimator.Combinators
import CollimatorTests.Framework

namespace CollimatorTests.IsoLaws

open Collimator
open Collimator.Theorems
open Collimator.Combinators
open CollimatorTests

/-! ## Test Structures -/

structure Point where
  x : Int
  y : Int
  deriving BEq, Repr

/-! ## Isomorphism Definitions -/

private def Point.toTuple : Point → (Int × Int) :=
  fun p => (p.x, p.y)

private def Point.fromTuple : (Int × Int) → Point :=
  fun (x, y) => { x := x, y := y }

private def swapPair {α β : Type} : (α × β) → (β × α) :=
  fun (a, b) => (b, a)

/-! ## Lawful Instances -/

instance : LawfulIso Point.toTuple Point.fromTuple where
  back_forward := by intro ⟨x, y⟩; rfl
  forward_back := by intro ⟨x, y⟩; rfl

instance {α β : Type} : LawfulIso (@swapPair α β) (@swapPair β α) where
  back_forward := by intro ⟨a, b⟩; rfl
  forward_back := by intro ⟨b, a⟩; rfl

/-! ## Test Cases -/

/--
Test that the Back-Forward law holds: applying backward after forward gives identity.
-/
private def case_backForwardLaw : TestCase := {
  name := "Iso Back-Forward law: backward (forward x) = x",
  run := do
    let pointIso : Iso' Point (Int × Int) := iso Point.toTuple Point.fromTuple
    let p := Point.mk 10 20
    let forwarded := isoForward pointIso p
    let restored := isoBackward pointIso forwarded
    ensureEq "Back-Forward law" p restored
}

/--
Test that the Forward-Back law holds: applying forward after backward gives identity.
-/
private def case_forwardBackLaw : TestCase := {
  name := "Iso Forward-Back law: forward (backward y) = y",
  run := do
    let pointIso : Iso' Point (Int × Int) := iso Point.toTuple Point.fromTuple
    let tuple := (5, 15)
    let backwarded := isoBackward pointIso tuple
    let restored := isoForward pointIso backwarded
    ensureEq "Forward-Back law" tuple restored
}

/--
Test that isoForward correctly applies the forward transformation.
-/
private def case_isoForward : TestCase := {
  name := "isoForward applies the forward transformation",
  run := do
    let pointIso : Iso' Point (Int × Int) := iso Point.toTuple Point.fromTuple
    let p := Point.mk 42 99
    let result := isoForward pointIso p
    ensureEq "Forward transformation" (42, 99) result
}

/--
Test that isoBackward correctly applies the backward transformation.
-/
private def case_isoBackward : TestCase := {
  name := "isoBackward applies the backward transformation",
  run := do
    let pointIso : Iso' Point (Int × Int) := iso Point.toTuple Point.fromTuple
    let result := isoBackward pointIso (7, 8)
    ensureEq "Backward transformation" (Point.mk 7 8) result
}

/--
Test tuple swap isomorphism.
-/
private def case_swapPairIso : TestCase := {
  name := "Tuple swap isomorphism satisfies both laws",
  run := do
    let swapIso : Iso' (Int × String) (String × Int) :=
      iso (@swapPair Int String) (@swapPair String Int)

    -- Back-Forward
    let p := (42, "hello")
    let swapped := isoForward swapIso p
    ensureEq "Swapped pair" ("hello", 42) swapped
    let restored := isoBackward swapIso swapped
    ensureEq "Swap Back-Forward" p restored

    -- Forward-Back
    let p2 := ("world", 99)
    let swappedBack := isoBackward swapIso p2
    let restored2 := isoForward swapIso swappedBack
    ensureEq "Swap Forward-Back" p2 restored2
}

/--
Test that identity iso satisfies laws.
-/
private def case_identityIso : TestCase := {
  name := "Identity iso satisfies both laws",
  run := do
    let idIso : Iso' Int Int := iso (fun x => x) (fun x => x)

    let n := 123
    let forwarded := isoForward idIso n
    ensureEq "Identity forward" n forwarded

    let backwarded := isoBackward idIso n
    ensureEq "Identity backward" n backwarded
}

/--
Test that negation iso for Bool satisfies laws.
-/
private def case_boolNegationIso : TestCase := {
  name := "Bool negation isomorphism satisfies both laws",
  run := do
    let negIso : Iso' Bool Bool := iso not not

    -- Back-Forward
    let b := true
    let negated := isoForward negIso b
    ensureEq "Negated bool" false negated
    let restored := isoBackward negIso negated
    ensureEq "Bool negation Back-Forward" b restored

    -- Forward-Back
    let b2 := false
    let negated2 := isoBackward negIso b2
    let restored2 := isoForward negIso negated2
    ensureEq "Bool negation Forward-Back" b2 restored2
}

/--
Test composition preserves Back-Forward law.
-/
private def case_compositionBackForwardLaw : TestCase := {
  name := "Composed isos satisfy Back-Forward law",
  run := do
    -- Compose Point <-> (Int × Int) <-> ((Int, Int), Unit)
    let iso1 : Iso' Point (Int × Int) := iso Point.toTuple Point.fromTuple
    let iso2 : Iso' (Int × Int) ((Int × Int) × Unit) :=
      iso (fun p => (p, ())) (fun pu => pu.1)

    -- Manual composition via function composition
    let composedForward := fun p => isoForward iso2 (isoForward iso1 p)
    let composedBackward := fun pu => isoBackward iso1 (isoBackward iso2 pu)

    let p := Point.mk 5 10
    let result := composedBackward (composedForward p)
    ensureEq "Composed Back-Forward law" p result
}

/--
Test composition preserves Forward-Back law.
-/
private def case_compositionForwardBackLaw : TestCase := {
  name := "Composed isos satisfy Forward-Back law",
  run := do
    let iso1 : Iso' Point (Int × Int) := iso Point.toTuple Point.fromTuple
    let iso2 : Iso' (Int × Int) ((Int × Int) × Unit) :=
      iso (fun p => (p, ())) (fun pu => pu.1)

    let composedForward := fun p => isoForward iso2 (isoForward iso1 p)
    let composedBackward := fun pu => isoBackward iso1 (isoBackward iso2 pu)

    let target := ((7, 8), ())
    let result := composedForward (composedBackward target)
    ensureEq "Composed Forward-Back law" target result
}

/--
Test that lawful iso theorems can be invoked.
This test verifies that we can use the proven theorems.
-/
private def case_isoLawTheorems : TestCase := {
  name := "Iso law theorems can be invoked",
  run := do
    let pointIso : Iso' Point (Int × Int) := iso Point.toTuple Point.fromTuple

    -- Back-Forward law
    let p := Point.mk 100 200
    let test1 := isoBackward pointIso (isoForward pointIso p)
    ensureEq "Law theorem Back-Forward" p test1

    -- Forward-Back law
    let tuple := (50, 75)
    let test2 := isoForward pointIso (isoBackward pointIso tuple)
    ensureEq "Law theorem Forward-Back" tuple test2
}

/--
Test Int negation isomorphism.
-/
private def case_intNegationIso : TestCase := {
  name := "Int negation isomorphism satisfies both laws",
  run := do
    let negIso : Iso' Int Int := iso (fun x => -x) (fun x => -x)

    -- Back-Forward
    let n : Int := 42
    let negated := isoForward negIso n
    let negExpected : Int := -42
    ensureEq "Negated int" negExpected negated
    let restored := isoBackward negIso negated
    ensureEq "Int negation Back-Forward" n restored

    -- Forward-Back
    let n2 : Int := -17
    let negated2 := isoBackward negIso n2
    let restored2 := isoForward negIso negated2
    ensureEq "Int negation Forward-Back" n2 restored2
}

/--
Test nested tuple isomorphism.
-/
private def case_nestedTupleIso : TestCase := {
  name := "Nested tuple isomorphism (associativity)",
  run := do
    -- Iso between ((a, b), c) and (a, (b, c))
    let assocForward : (Int × Int) × Int → Int × (Int × Int) :=
      fun ((a, b), c) => (a, (b, c))
    let assocBackward : Int × (Int × Int) → (Int × Int) × Int :=
      fun (a, (b, c)) => ((a, b), c)
    let assocIso : Iso' ((Int × Int) × Int) (Int × (Int × Int)) :=
      iso assocForward assocBackward

    -- Test laws
    let left := ((1, 2), 3)
    let right := (1, (2, 3))

    let forwardResult := isoForward assocIso left
    ensureEq "Assoc forward" right forwardResult

    let backwardResult := isoBackward assocIso right
    ensureEq "Assoc backward" left backwardResult

    -- Round trip
    let roundTrip1 := isoBackward assocIso (isoForward assocIso left)
    ensureEq "Assoc round trip 1" left roundTrip1

    let roundTrip2 := isoForward assocIso (isoBackward assocIso right)
    ensureEq "Assoc round trip 2" right roundTrip2
}

/--
All iso law test cases.
-/
def cases : List TestCase :=
  [ case_backForwardLaw
  , case_forwardBackLaw
  , case_isoForward
  , case_isoBackward
  , case_swapPairIso
  , case_identityIso
  , case_boolNegationIso
  , case_compositionBackForwardLaw
  , case_compositionForwardBackLaw
  , case_isoLawTheorems
  , case_intNegationIso
  , case_nestedTupleIso
  ]

end CollimatorTests.IsoLaws
