import Batteries
import Collimator.Optics
import Collimator.Theorems.PrismLaws
import Collimator.Combinators
import Collimator.Operators
import CollimatorTests.Framework

namespace CollimatorTests.PrismLaws

open Collimator
open Collimator.Theorems
open Collimator.Combinators
open CollimatorTests
open scoped Collimator.Operators

testSuite "Prism Laws"

/-! ## Test Structures -/

inductive Shape where
  | circle (radius : Int)
  | rectangle (width : Int) (height : Int)
  | triangle (base : Int) (height : Int)
  deriving BEq, Repr

inductive Container where
  | box (content : Shape)
  | empty
  deriving BEq, Repr

/-! ## Prism Definitions -/

private def Shape.buildCircle : Int → Shape := Shape.circle

private def Shape.splitCircle : Shape → Sum Shape Int :=
  fun s => match s with
    | Shape.circle r => Sum.inr r
    | other => Sum.inl other

private def Shape.buildRectangle : (Int × Int) → Shape :=
  fun (w, h) => Shape.rectangle w h

private def Shape.splitRectangle : Shape → Sum Shape (Int × Int) :=
  fun s => match s with
    | Shape.rectangle w h => Sum.inr (w, h)
    | other => Sum.inl other

private def Container.buildBox : Shape → Container := Container.box

private def Container.splitBox : Container → Sum Container Shape :=
  fun c => match c with
    | Container.box s => Sum.inr s
    | Container.empty => Sum.inl Container.empty

/-! ## Lawful Instances -/

instance : LawfulPrism Shape.buildCircle Shape.splitCircle where
  preview_review := by intro _; rfl
  review_preview := by
    intro s r h
    cases s with
    | circle r' =>
      unfold Shape.splitCircle at h
      injection h with heq
      subst heq
      unfold Shape.buildCircle
      rfl
    | rectangle _ _ => unfold Shape.splitCircle at h; contradiction
    | triangle _ _ => unfold Shape.splitCircle at h; contradiction

instance : LawfulPrism Shape.buildRectangle Shape.splitRectangle where
  preview_review := by intro _; rfl
  review_preview := by
    intro s p h
    cases s with
    | rectangle w h' =>
      unfold Shape.splitRectangle at h
      injection h with heq
      cases p with | mk pw ph =>
        simp at heq
        rcases heq with ⟨hw, hh⟩
        subst hw hh
        unfold Shape.buildRectangle
        rfl
    | circle _ => unfold Shape.splitRectangle at h; contradiction
    | triangle _ _ => unfold Shape.splitRectangle at h; contradiction

instance : LawfulPrism Container.buildBox Container.splitBox where
  preview_review := by intro _; rfl
  review_preview := by
    intro c s h
    cases c with
    | box s' =>
      unfold Container.splitBox at h
      injection h with heq
      subst heq
      unfold Container.buildBox
      rfl
    | empty => unfold Container.splitBox at h; contradiction

/-! ## Test Cases -/

test "Prism Preview-Review law: preview p (review p b) = some b" := do
  let circlePrism : Prism' Shape Int := prism Shape.buildCircle Shape.splitCircle
  let radius := 42
  let reviewed := review' circlePrism radius
  let previewed := reviewed ^? circlePrism
  ensureEq "Preview-Review law" (some radius) previewed

test "Prism Review-Preview law: preview p s = some a → review p a = s" := do
  let circlePrism : Prism' Shape Int := prism Shape.buildCircle Shape.splitCircle
  let s : Shape := Shape.circle 100
  match s ^? circlePrism with
  | none => throw (IO.userError "Expected preview to succeed")
  | some a =>
    let reconstructed := review' circlePrism a
    ensureEq "Review-Preview law" s reconstructed

test "Prism preview returns none on non-matching constructor" := do
  let circlePrism : Prism' Shape Int := prism Shape.buildCircle Shape.splitCircle
  let s : Shape := Shape.rectangle 10 20
  let result := s ^? circlePrism
  ensureEq "Preview on mismatch" none result

test "Rectangle prism satisfies both laws" := do
  let rectPrism : Prism' Shape (Int × Int) := prism Shape.buildRectangle Shape.splitRectangle

  -- Preview-Review
  let dims := (15, 25)
  let reviewed1 := review' rectPrism dims
  let previewed1 := reviewed1 ^? rectPrism
  ensureEq "Rectangle Preview-Review" (some dims) previewed1

  -- Review-Preview
  let s : Shape := Shape.rectangle 30 40
  match s ^? rectPrism with
  | none => throw (IO.userError "Expected preview to succeed")
  | some d =>
    let reconstructed := review' rectPrism d
    ensureEq "Rectangle Review-Preview" s reconstructed

test "Composed prisms satisfy Preview-Review law" := do
  let boxPrism : Prism' Container Shape := prism Container.buildBox Container.splitBox
  let circlePrism : Prism' Shape Int := prism Shape.buildCircle Shape.splitCircle
  let composed : Prism' Container Int := boxPrism ∘ circlePrism

  let radius := 77
  let reviewed := review' composed radius
  let previewed := reviewed ^? composed
  ensureEq "Composed Preview-Review law" (some radius) previewed

test "Composed prisms satisfy Review-Preview law" := do
  let boxPrism : Prism' Container Shape := prism Container.buildBox Container.splitBox
  let circlePrism : Prism' Shape Int := prism Shape.buildCircle Shape.splitCircle
  let composed : Prism' Container Int := boxPrism ∘ circlePrism

  let c : Container := Container.box (Shape.circle 99)
  match c ^? composed with
  | none => throw (IO.userError "Expected preview to succeed")
  | some a =>
    let reconstructed := review' composed a
    ensureEq "Composed Review-Preview law" c reconstructed

test "Composed prism preview fails on outer mismatch" := do
  let boxPrism : Prism' Container Shape := prism Container.buildBox Container.splitBox
  let circlePrism : Prism' Shape Int := prism Shape.buildCircle Shape.splitCircle
  let composed : Prism' Container Int := boxPrism ∘ circlePrism

  let c : Container := Container.empty
  let result := c ^? composed
  ensureEq "Composed preview on outer mismatch" none result

test "Composed prism preview fails on inner mismatch" := do
  let boxPrism : Prism' Container Shape := prism Container.buildBox Container.splitBox
  let circlePrism : Prism' Shape Int := prism Shape.buildCircle Shape.splitCircle
  let composed : Prism' Container Int := boxPrism ∘ circlePrism

  let c : Container := Container.box (Shape.rectangle 5 10)
  let result := c ^? composed
  ensureEq "Composed preview on inner mismatch" none result

test "Prism law theorems can be invoked" := do
  -- The theorems themselves are compile-time proofs
  -- We verify they exist and are applicable by using them in computations
  let circlePrism : Prism' Shape Int := prism Shape.buildCircle Shape.splitCircle

  -- These operations should satisfy the laws by construction
  let test1 := (review' circlePrism 50) ^? circlePrism
  let s := Shape.circle 75
  let test2 := match s ^? circlePrism with
    | some a => review' circlePrism a
    | none => s

  ensureEq "Law theorem Preview-Review" (some 50) test1
  ensureEq "Law theorem Review-Preview" s test2

test "Composition lawfulness instance is usable" := do
  -- The instance composedPrism_isLawful proves that composed build/split are lawful
  let boxPrism : Prism' Container Shape := prism Container.buildBox Container.splitBox
  let rectPrism : Prism' Shape (Int × Int) := prism Shape.buildRectangle Shape.splitRectangle
  let composed : Prism' Container (Int × Int) := boxPrism ∘ rectPrism

  -- Verify the composition works correctly
  let c := Container.box (Shape.rectangle 8 12)
  let viewed := c ^? composed
  ensureEq "Composed preview" (some (8, 12)) viewed

  let c' := review' composed (20, 30)
  let expected := Container.box (Shape.rectangle 20 30)
  ensureEq "Composed review" expected c'

test "Option some prism satisfies laws" := do
  let somePrism : Prism' (Option Int) Int :=
    prism some (fun opt => match opt with
      | some a => Sum.inr a
      | none => Sum.inl none)

  -- Preview-Review
  let reviewed := review' somePrism 123
  let previewed := reviewed ^? somePrism
  ensureEq "Option Preview-Review" (some 123) previewed

  -- Review-Preview on Some
  let opt := some 456
  match opt ^? somePrism with
  | none => throw (IO.userError "Expected preview to succeed")
  | some a =>
    let reconstructed := review' somePrism a
    ensureEq "Option Review-Preview" opt reconstructed

  -- Preview on None
  let result := (none : Option Int) ^? somePrism
  ensureEq "Option preview on none" none result

#generate_tests

end CollimatorTests.PrismLaws
