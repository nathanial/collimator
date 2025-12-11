import Collimator.Core
import Collimator.Optics
import CollimatorTests.Framework

namespace CollimatorTests.GetterReview

open Collimator
open Collimator.Core
open CollimatorTests

/-!
# Getter and Review Optics Tests

Tests for the read-only Getter optic and the write-only Review optic.
-/

testSuite "Getter and Review"

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

test "Getter: basic construction and view" := do
  -- Create a simple getter
  let nameGetter := getter (fun p : Person => p.name)
  let alice := Person.mk "Alice" 30

  -- Use view
  let name := nameGetter.view alice
  name ≡ "Alice"

  -- Use coercion (getter as function)
  let name2 := nameGetter alice
  name2 ≡ "Alice"

  IO.println "✓ Getter: basic construction and view"

test "Getter: conversion from Lens (ofLens)" := do
  let bob := Person.mk "Bob" 25

  -- Convert lens to getter
  let ageGetter := Getter.ofLens personAgeLens

  let age := ageGetter.view bob
  age ≡ 25

  -- Getters are read-only - can only view, not set
  -- (This is enforced by the type system)

  IO.println "✓ Getter: conversion from Lens works correctly"

test "Getter: composition of getters" := do
  let company := Company.mk "TechCorp" (Person.mk "Carol" 45)

  -- Create getters
  let ceoGetter := Getter.ofLens companyCeoLens
  let ageGetter := Getter.ofLens personAgeLens

  -- Compose getters
  let ceoAgeGetter := ceoGetter.compose ageGetter

  let ceoAge := ceoAgeGetter.view company
  ceoAge ≡ 45

  -- Compose with name
  let nameGetter := Getter.ofLens personNameLens
  let ceoNameGetter := ceoGetter.compose nameGetter

  let ceoName := ceoNameGetter.view company
  ceoName ≡ "Carol"

  IO.println "✓ Getter: composition works correctly"

test "Getter: practical use cases" := do
  let people := [
    Person.mk "Alice" 30,
    Person.mk "Bob" 25,
    Person.mk "Carol" 35
  ]

  let nameGetter := getter (fun p : Person => p.name)
  let ageGetter := getter (fun p : Person => p.age)

  -- Extract all names
  let names := people.map nameGetter.view
  names ≡ ["Alice", "Bob", "Carol"]

  -- Find average age using getter
  let ages := people.map ageGetter.view
  let totalAge := ages.foldl (· + ·) 0
  totalAge ≡ 90

  -- Computed getter (derived value)
  let isAdultGetter := getter (fun p : Person => decide (p.age >= 18))
  let allAdults := people.map isAdultGetter.view
  shouldSatisfy (allAdults.all (fun b => b)) "all adults"

  IO.println "✓ Getter: practical use cases work correctly"

-- ## Review Tests

test "Review: basic construction and review" := do
  -- Create a simple review (constructor)
  let personReview := mkReview (fun pair : String × Nat => Person.mk pair.1 pair.2)

  -- Use review to construct
  let alice := personReview.review ("Alice", 30)
  alice ≡ Person.mk "Alice" 30

  -- Use coercion (review as function)
  let bob := personReview ("Bob", 25)
  bob ≡ Person.mk "Bob" 25

  IO.println "✓ Review: basic construction and review"

test "Review: conversion from Prism (ofPrism)" := do
  -- Convert prism to review
  let circleReview := Review.ofPrism circlePrism

  -- Use review to construct
  let circle := circleReview.review 5.0
  circle ≡ Shape.circle 5.0

  -- Rect prism
  let rectReview := Review.ofPrism rectPrism
  let rect := rectReview.review (10.0, 20.0)
  rect ≡ Shape.rect 10.0 20.0

  IO.println "✓ Review: conversion from Prism works correctly"

test "Review: conversion from Iso (ofIso)" := do
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
  pair ≡ (42, "hello")

  let pair2 := swapReview.review ("world", 100)
  pair2 ≡ (100, "world")

  IO.println "✓ Review: conversion from Iso works correctly"

test "Review: composition of reviews" := do
  -- Create reviews
  let circleReview := Review.ofPrism circlePrism

  -- Create a review that builds Option Shape from Float
  let optionReview := mkReview (fun s : Shape => some s)

  -- Compose: Float → Shape → Option Shape
  let optCircleReview := optionReview.compose circleReview

  let optCircle := optCircleReview.review 7.5
  optCircle ≡ some (Shape.circle 7.5)

  IO.println "✓ Review: composition works correctly"

test "Review: practical use cases" := do
  -- Factory pattern using Review
  let circleFactory := Review.ofPrism circlePrism
  let rectFactory := Review.ofPrism rectPrism

  -- Build shapes from data
  let radii := [1.0, 2.0, 3.0]
  let circles := radii.map circleFactory.review
  circles.length ≡ 3

  -- Build from tuples
  let dims := [(1.0, 2.0), (3.0, 4.0)]
  let rects := dims.map rectFactory.review
  rects.length ≡ 2

  -- Smart constructor pattern
  let validPersonReview := mkReview (fun pair : String × Nat =>
    if pair.1.length > 0 && pair.2 > 0 then Person.mk pair.1 pair.2 else Person.mk "Invalid" 0
  )

  let validPerson := validPersonReview.review ("Dave", 40)
  validPerson.name ≡ "Dave"

  let invalidPerson := validPersonReview.review ("", 0)
  invalidPerson.name ≡ "Invalid"

  IO.println "✓ Review: practical use cases work correctly"

test "Getter/Review: demonstrating duality" := do
  -- Getter: read-only, extracts from structure
  let ageGetter := Getter.ofLens personAgeLens

  -- Review: write-only, builds structure
  let circleReview := Review.ofPrism circlePrism

  -- Getter extracts
  let person := Person.mk "Eve" 28
  let extractedAge := ageGetter.view person
  extractedAge ≡ 28

  -- Review constructs
  let constructedShape := circleReview.review 10.0
  constructedShape ≡ Shape.circle 10.0

  -- They are dual operations:
  -- Getter: S → A (extract focus from whole)
  -- Review: B → T (construct whole from focus)

  IO.println "✓ Getter/Review: duality demonstrated"

#generate_tests

end CollimatorTests.GetterReview
