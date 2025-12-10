import Collimator.Optics
import Collimator.Core.Profunctor
import CollimatorTests.Framework

namespace CollimatorTests.GetterReview

open Collimator
open Collimator.Core
open CollimatorTests

/-!
# Getter and Review Optics Tests

Tests for the read-only Getter optic and the write-only Review optic.
-/

-- ## Test Data Types

structure Person where
  name : String
  age : Nat
  deriving BEq, Repr, Inhabited

structure Company where
  name : String
  ceo : Person
  deriving BEq, Repr, Inhabited

inductive Shape : Type where
  | circle : Float → Shape        -- radius
  | rect : Float → Float → Shape  -- width × height
  deriving BEq, Repr, Inhabited

-- ## Lenses and Prisms for testing

def personNameLens : Lens' Person String :=
  lens' (fun p => p.name) (fun p n => { p with name := n })

def personAgeLens : Lens' Person Nat :=
  lens' (fun p => p.age) (fun p a => { p with age := a })

def companyNameLens : Lens' Company String :=
  lens' (fun c => c.name) (fun c n => { c with name := n })

def companyCeoLens : Lens' Company Person :=
  lens' (fun c => c.ceo) (fun c p => { c with ceo := p })

def circlePrism : Prism' Shape Float :=
  prism (fun r => Shape.circle r)
        (fun s => match s with
         | Shape.circle r => Sum.inr r
         | other => Sum.inl other)

def rectPrism : Prism' Shape (Float × Float) :=
  prism (fun (w, h) => Shape.rect w h)
        (fun s => match s with
         | Shape.rect w h => Sum.inr (w, h)
         | other => Sum.inl other)

-- ## Getter Tests

/-- Basic Getter construction and use -/
def case_getterBasics : TestCase := {
  name := "Getter: basic construction and view",
  run := do
    -- Create a simple getter
    let nameGetter := getter (fun p : Person => p.name)
    let alice := Person.mk "Alice" 30

    -- Use view
    let name := nameGetter.view alice
    if name != "Alice" then
      throw (IO.userError s!"Expected Alice, got {name}")

    -- Use coercion (getter as function)
    let name2 := nameGetter alice
    if name2 != "Alice" then
      throw (IO.userError s!"Expected Alice from coercion, got {name2}")

    IO.println "✓ Getter: basic construction and view"
}

/-- Getter from Lens conversion -/
def case_getterFromLens : TestCase := {
  name := "Getter: conversion from Lens (ofLens)",
  run := do
    let bob := Person.mk "Bob" 25

    -- Convert lens to getter
    let ageGetter := Getter.ofLens personAgeLens

    let age := ageGetter.view bob
    if age != 25 then
      throw (IO.userError s!"Expected 25, got {age}")

    -- Getters are read-only - can only view, not set
    -- (This is enforced by the type system)

    IO.println "✓ Getter: conversion from Lens works correctly"
}

/-- Getter composition -/
def case_getterComposition : TestCase := {
  name := "Getter: composition of getters",
  run := do
    let company := Company.mk "TechCorp" (Person.mk "Carol" 45)

    -- Create getters
    let ceoGetter := Getter.ofLens companyCeoLens
    let ageGetter := Getter.ofLens personAgeLens

    -- Compose getters
    let ceoAgeGetter := ceoGetter.compose ageGetter

    let ceoAge := ceoAgeGetter.view company
    if ceoAge != 45 then
      throw (IO.userError s!"Expected 45, got {ceoAge}")

    -- Compose with name
    let nameGetter := Getter.ofLens personNameLens
    let ceoNameGetter := ceoGetter.compose nameGetter

    let ceoName := ceoNameGetter.view company
    if ceoName != "Carol" then
      throw (IO.userError s!"Expected Carol, got {ceoName}")

    IO.println "✓ Getter: composition works correctly"
}

/-- Getter use cases -/
def case_getterUseCases : TestCase := {
  name := "Getter: practical use cases",
  run := do
    let people := [
      Person.mk "Alice" 30,
      Person.mk "Bob" 25,
      Person.mk "Carol" 35
    ]

    let nameGetter := getter (fun p : Person => p.name)
    let ageGetter := getter (fun p : Person => p.age)

    -- Extract all names
    let names := people.map nameGetter.view
    if names != ["Alice", "Bob", "Carol"] then
      throw (IO.userError s!"Expected names list, got {repr names}")

    -- Find average age using getter
    let ages := people.map ageGetter.view
    let totalAge := ages.foldl (· + ·) 0
    if totalAge != 90 then
      throw (IO.userError s!"Expected total 90, got {totalAge}")

    -- Computed getter (derived value)
    let isAdultGetter := getter (fun p : Person => decide (p.age >= 18))
    let allAdults := people.map isAdultGetter.view
    if !allAdults.all (fun b => b) then
      throw (IO.userError "Expected all adults")

    IO.println "✓ Getter: practical use cases work correctly"
}

-- ## Review Tests

/-- Basic Review construction and use -/
def case_reviewBasics : TestCase := {
  name := "Review: basic construction and review",
  run := do
    -- Create a simple review (constructor)
    let personReview := mkReview (fun pair : String × Nat => Person.mk pair.1 pair.2)

    -- Use review to construct
    let alice := personReview.review ("Alice", 30)
    if alice.name != "Alice" || alice.age != 30 then
      throw (IO.userError s!"Expected Person Alice 30, got {repr alice}")

    -- Use coercion (review as function)
    let bob := personReview ("Bob", 25)
    if bob.name != "Bob" || bob.age != 25 then
      throw (IO.userError s!"Expected Person Bob 25, got {repr bob}")

    IO.println "✓ Review: basic construction and review"
}

/-- Review from Prism conversion -/
def case_reviewFromPrism : TestCase := {
  name := "Review: conversion from Prism (ofPrism)",
  run := do
    -- Convert prism to review
    let circleReview := Review.ofPrism circlePrism

    -- Use review to construct
    let circle := circleReview.review 5.0
    if circle != Shape.circle 5.0 then
      throw (IO.userError s!"Expected circle 5.0, got {repr circle}")

    -- Rect prism
    let rectReview := Review.ofPrism rectPrism
    let rect := rectReview.review (10.0, 20.0)
    if rect != Shape.rect 10.0 20.0 then
      throw (IO.userError s!"Expected rect 10 20, got {repr rect}")

    IO.println "✓ Review: conversion from Prism works correctly"
}

/-- Review from Iso conversion -/
def case_reviewFromIso : TestCase := {
  name := "Review: conversion from Iso (ofIso)",
  run := do
    -- For iso with focus type a and source type s, review gives us a → s (backwards)
    -- So for an Iso' s a, Review.ofIso gives us a Review s a where
    -- review r a gives us s.

    -- Create an iso that swaps tuple components using library function
    let swapIso : Iso' (Int × String) (String × Int) :=
      iso (fun (a, b) => (b, a)) (fun (b, a) => (a, b))

    -- Convert iso to review
    let swapReview := Review.ofIso swapIso

    -- Use review to construct (Int × String) from (String × Int)
    let pair := swapReview.review ("hello", 42)
    if pair != (42, "hello") then
      throw (IO.userError s!"Expected (42, hello), got {repr pair}")

    let pair2 := swapReview.review ("world", 100)
    if pair2 != (100, "world") then
      throw (IO.userError s!"Expected (100, world), got {repr pair2}")

    IO.println "✓ Review: conversion from Iso works correctly"
}

/-- Review composition -/
def case_reviewComposition : TestCase := {
  name := "Review: composition of reviews",
  run := do
    -- Create reviews
    let circleReview := Review.ofPrism circlePrism

    -- Create a review that builds Option Shape from Float
    let optionReview := mkReview (fun s : Shape => some s)

    -- Compose: Float → Shape → Option Shape
    let optCircleReview := optionReview.compose circleReview

    let optCircle := optCircleReview.review 7.5
    if optCircle != some (Shape.circle 7.5) then
      throw (IO.userError s!"Expected some (circle 7.5), got {repr optCircle}")

    IO.println "✓ Review: composition works correctly"
}

/-- Review use cases -/
def case_reviewUseCases : TestCase := {
  name := "Review: practical use cases",
  run := do
    -- Factory pattern using Review
    let circleFactory := Review.ofPrism circlePrism
    let rectFactory := Review.ofPrism rectPrism

    -- Build shapes from data
    let radii := [1.0, 2.0, 3.0]
    let circles := radii.map circleFactory.review
    if circles.length != 3 then
      throw (IO.userError s!"Expected 3 circles, got {circles.length}")

    -- Build from tuples
    let dims := [(1.0, 2.0), (3.0, 4.0)]
    let rects := dims.map rectFactory.review
    if rects.length != 2 then
      throw (IO.userError s!"Expected 2 rects, got {rects.length}")

    -- Smart constructor pattern
    let validPersonReview := mkReview (fun pair : String × Nat =>
      if pair.1.length > 0 && pair.2 > 0 then Person.mk pair.1 pair.2 else Person.mk "Invalid" 0
    )

    let validPerson := validPersonReview.review ("Dave", 40)
    if validPerson.name != "Dave" then
      throw (IO.userError s!"Expected Dave, got {validPerson.name}")

    let invalidPerson := validPersonReview.review ("", 0)
    if invalidPerson.name != "Invalid" then
      throw (IO.userError s!"Expected Invalid, got {invalidPerson.name}")

    IO.println "✓ Review: practical use cases work correctly"
}

/-- Getter and Review duality -/
def case_getterReviewDuality : TestCase := {
  name := "Getter/Review: demonstrating duality",
  run := do
    -- Getter: read-only, extracts from structure
    let ageGetter := Getter.ofLens personAgeLens

    -- Review: write-only, builds structure
    let circleReview := Review.ofPrism circlePrism

    -- Getter extracts
    let person := Person.mk "Eve" 28
    let extractedAge := ageGetter.view person
    if extractedAge != 28 then
      throw (IO.userError s!"Expected 28, got {extractedAge}")

    -- Review constructs
    let constructedShape := circleReview.review 10.0
    if constructedShape != Shape.circle 10.0 then
      throw (IO.userError s!"Expected circle 10.0, got {repr constructedShape}")

    -- They are dual operations:
    -- Getter: S → A (extract focus from whole)
    -- Review: B → T (construct whole from focus)

    IO.println "✓ Getter/Review: duality demonstrated"
}

-- ## Test Registration

def cases : List TestCase := [
  -- Getter tests
  case_getterBasics,
  case_getterFromLens,
  case_getterComposition,
  case_getterUseCases,
  -- Review tests
  case_reviewBasics,
  case_reviewFromPrism,
  case_reviewFromIso,
  case_reviewComposition,
  case_reviewUseCases,
  -- Duality
  case_getterReviewDuality
]

end CollimatorTests.GetterReview
