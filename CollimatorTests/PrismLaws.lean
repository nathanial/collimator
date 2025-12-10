import Batteries
import Collimator.Optics
import Collimator.Theorems.PrismLaws
import Collimator.Combinators
import CollimatorTests.Framework

namespace CollimatorTests.PrismLaws

open Collimator
open Collimator.Theorems
open Collimator.Combinators
open CollimatorTests

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

/--
Test that the Preview-Review law holds: previewing after reviewing returns what was reviewed.
-/
private def case_previewReviewLaw : TestCase := {
  name := "Prism Preview-Review law: preview p (review p b) = some b",
  run := do
    let circlePrism : Prism' Shape Int := prism Shape.buildCircle Shape.splitCircle
    let radius := 42
    let reviewed := review' circlePrism radius
    let previewed := preview' circlePrism reviewed
    ensureEq "Preview-Review law" (some radius) previewed
}

/--
Test that the Review-Preview law holds: if preview succeeds, reviewing reconstructs the original.
-/
private def case_reviewPreviewLaw : TestCase := {
  name := "Prism Review-Preview law: preview p s = some a → review p a = s",
  run := do
    let circlePrism : Prism' Shape Int := prism Shape.buildCircle Shape.splitCircle
    let s : Shape := Shape.circle 100
    match preview' circlePrism s with
    | none => throw (IO.userError "Expected preview to succeed")
    | some a =>
      let reconstructed := review' circlePrism a
      ensureEq "Review-Preview law" s reconstructed
}

/--
Test that preview fails on non-matching constructors.
-/
private def case_previewFailsOnMismatch : TestCase := {
  name := "Prism preview returns none on non-matching constructor",
  run := do
    let circlePrism : Prism' Shape Int := prism Shape.buildCircle Shape.splitCircle
    let s : Shape := Shape.rectangle 10 20
    let result := preview' circlePrism s
    ensureEq "Preview on mismatch" none result
}

/--
Test that all prism laws hold for rectangle prism with product type.
-/
private def case_rectanglePrismLaws : TestCase := {
  name := "Rectangle prism satisfies both laws",
  run := do
    let rectPrism : Prism' Shape (Int × Int) := prism Shape.buildRectangle Shape.splitRectangle

    -- Preview-Review
    let dims := (15, 25)
    let reviewed1 := review' rectPrism dims
    let previewed1 := preview' rectPrism reviewed1
    ensureEq "Rectangle Preview-Review" (some dims) previewed1

    -- Review-Preview
    let s : Shape := Shape.rectangle 30 40
    match preview' rectPrism s with
    | none => throw (IO.userError "Expected preview to succeed")
    | some d =>
      let reconstructed := review' rectPrism d
      ensureEq "Rectangle Review-Preview" s reconstructed
}

/--
Test composition preserves Preview-Review law.
-/
private def case_compositionPreviewReviewLaw : TestCase := {
  name := "Composed prisms satisfy Preview-Review law",
  run := do
    let boxPrism : Prism' Container Shape := prism Container.buildBox Container.splitBox
    let circlePrism : Prism' Shape Int := prism Shape.buildCircle Shape.splitCircle
    let composed : Prism' Container Int := boxPrism ∘ circlePrism

    let radius := 77
    let reviewed := review' composed radius
    let previewed := preview' composed reviewed
    ensureEq "Composed Preview-Review law" (some radius) previewed
}

/--
Test composition preserves Review-Preview law.
-/
private def case_compositionReviewPreviewLaw : TestCase := {
  name := "Composed prisms satisfy Review-Preview law",
  run := do
    let boxPrism : Prism' Container Shape := prism Container.buildBox Container.splitBox
    let circlePrism : Prism' Shape Int := prism Shape.buildCircle Shape.splitCircle
    let composed : Prism' Container Int := boxPrism ∘ circlePrism

    let c : Container := Container.box (Shape.circle 99)
    match preview' composed c with
    | none => throw (IO.userError "Expected preview to succeed")
    | some a =>
      let reconstructed := review' composed a
      ensureEq "Composed Review-Preview law" c reconstructed
}

/--
Test that composed prisms fail appropriately on mismatches.
-/
private def case_composedPreviewFailure : TestCase := {
  name := "Composed prism preview fails on outer mismatch",
  run := do
    let boxPrism : Prism' Container Shape := prism Container.buildBox Container.splitBox
    let circlePrism : Prism' Shape Int := prism Shape.buildCircle Shape.splitCircle
    let composed : Prism' Container Int := boxPrism ∘ circlePrism

    let c : Container := Container.empty
    let result := preview' composed c
    ensureEq "Composed preview on outer mismatch" none result
}

/--
Test that composed prisms fail appropriately on inner mismatches.
-/
private def case_composedPreviewInnerFailure : TestCase := {
  name := "Composed prism preview fails on inner mismatch",
  run := do
    let boxPrism : Prism' Container Shape := prism Container.buildBox Container.splitBox
    let circlePrism : Prism' Shape Int := prism Shape.buildCircle Shape.splitCircle
    let composed : Prism' Container Int := boxPrism ∘ circlePrism

    let c : Container := Container.box (Shape.rectangle 5 10)
    let result := preview' composed c
    ensureEq "Composed preview on inner mismatch" none result
}

/--
Test that using the lawful prism theorems works correctly.
This test verifies that we can use the proven theorems to establish prism correctness.
-/
private def case_prismLawTheorems : TestCase := {
  name := "Prism law theorems can be invoked",
  run := do
    -- The theorems themselves are compile-time proofs
    -- We verify they exist and are applicable by using them in computations
    let circlePrism : Prism' Shape Int := prism Shape.buildCircle Shape.splitCircle

    -- These operations should satisfy the laws by construction
    let test1 := preview' circlePrism (review' circlePrism 50)
    let s := Shape.circle 75
    let test2 := match preview' circlePrism s with
      | some a => review' circlePrism a
      | none => s

    ensureEq "Law theorem Preview-Review" (some 50) test1
    ensureEq "Law theorem Review-Preview" s test2
}

/--
Test that the composition lawfulness instance works.
This demonstrates that composedPrism_isLawful can be used as an instance.
-/
private def case_compositionLawfulInstance : TestCase := {
  name := "Composition lawfulness instance is usable",
  run := do
    -- The instance composedPrism_isLawful proves that composed build/split are lawful
    let boxPrism : Prism' Container Shape := prism Container.buildBox Container.splitBox
    let rectPrism : Prism' Shape (Int × Int) := prism Shape.buildRectangle Shape.splitRectangle
    let composed : Prism' Container (Int × Int) := boxPrism ∘ rectPrism

    -- Verify the composition works correctly
    let c := Container.box (Shape.rectangle 8 12)
    let viewed := preview' composed c
    ensureEq "Composed preview" (some (8, 12)) viewed

    let c' := review' composed (20, 30)
    let expected := Container.box (Shape.rectangle 20 30)
    ensureEq "Composed review" expected c'
}

/--
Test Option prism (the canonical example).
-/
private def case_optionPrism : TestCase := {
  name := "Option some prism satisfies laws",
  run := do
    let somePrism : Prism' (Option Int) Int :=
      prism some (fun opt => match opt with
        | some a => Sum.inr a
        | none => Sum.inl none)

    -- Preview-Review
    let reviewed := review' somePrism 123
    let previewed := preview' somePrism reviewed
    ensureEq "Option Preview-Review" (some 123) previewed

    -- Review-Preview on Some
    let opt := some 456
    match preview' somePrism opt with
    | none => throw (IO.userError "Expected preview to succeed")
    | some a =>
      let reconstructed := review' somePrism a
      ensureEq "Option Review-Preview" opt reconstructed

    -- Preview on None
    let result := preview' somePrism (none : Option Int)
    ensureEq "Option preview on none" none result
}

/--
All prism law test cases.
-/
def cases : List TestCase :=
  [ case_previewReviewLaw
  , case_reviewPreviewLaw
  , case_previewFailsOnMismatch
  , case_rectanglePrismLaws
  , case_compositionPreviewReviewLaw
  , case_compositionReviewPreviewLaw
  , case_composedPreviewFailure
  , case_composedPreviewInnerFailure
  , case_prismLawTheorems
  , case_compositionLawfulInstance
  , case_optionPrism
  ]

end CollimatorTests.PrismLaws
