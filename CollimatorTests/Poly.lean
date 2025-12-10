import Batteries
import Collimator.Poly
import Collimator.Optics
import Collimator.Theorems.IsoLaws
import Collimator.Instances
import CollimatorTests.Framework

open Collimator.Instances.Option

namespace CollimatorTests.Poly

open Batteries
open Collimator.Poly  -- Only open the polymorphic namespace
open Collimator  -- Import lens and iso constructors
open Collimator.Traversal (eachList)  -- Import eachList
open Collimator.AffineTraversalOps (ofPrism)  -- Import ofPrism
open CollimatorTests

/-!
# Polymorphic Optics API Tests

This test suite validates that the polymorphic API works correctly across
all optic types (Iso, Lens, Prism, AffineTraversal, Traversal).

Each test demonstrates:
1. Type class resolution works correctly
2. Operations produce expected results
3. Polymorphic functions work across multiple optic types
-/

/-! ## Test Data Types -/

structure Point where
  x : Float
  y : Float
  deriving BEq, Repr

structure Complex where
  real : Float
  imag : Float
  deriving BEq, Repr

/-! ## Section 1: Iso Tests -/
namespace IsoTests

/-- Iso between Complex and (Float × Float) -/
private def complexIso : Collimator.Iso' Complex (Float × Float) :=
  iso
    (forward := fun c => (c.real, c.imag))
    (back := fun (r, i) => { real := r, imag := i })

private def case_iso_view : TestCase := {
  name := "Poly: Iso supports view",
  run := do
    let c : Complex := { real := 3.0, imag := 4.0 }
    let pair := view (optic := fun s a => Iso s s a a) complexIso c
    ensureEq "view extracts pair" (3.0, 4.0) pair
}

private def case_iso_over : TestCase := {
  name := "Poly: Iso supports over",
  run := do
    let c : Complex := { real := 3.0, imag := 4.0 }
    let c' := over (optic := Iso) complexIso (fun (r, i) => (r * 2.0, i * 2.0)) c
    ensureEq "over transforms" (Complex.mk 6.0 8.0) c'
}

private def case_iso_set : TestCase := {
  name := "Poly: Iso supports set",
  run := do
    let c : Complex := { real := 3.0, imag := 4.0 }
    let c' := set (optic := Iso) complexIso (5.0, 12.0) c
    ensureEq "set replaces" (Complex.mk 5.0 12.0) c'
}

private def case_iso_preview : TestCase := {
  name := "Poly: Iso supports preview (always succeeds)",
  run := do
    let c : Complex := { real := 3.0, imag := 4.0 }
    let result := preview (optic := fun s a => Iso s s a a) complexIso c
    ensureEq "preview succeeds" (some (3.0, 4.0)) result
}

private def case_iso_review : TestCase := {
  name := "Poly: Iso supports review",
  run := do
    let c := review (optic := Iso) complexIso (5.0, 12.0)
    ensureEq "review constructs" (Complex.mk 5.0 12.0) c
}

private def case_iso_traverse : TestCase := {
  name := "Poly: Iso supports traverse",
  run := do
    let c : Complex := { real := 3.0, imag := 4.0 }
    -- Traverse with Option (double if both coords < 10)
    let result := traverse (optic := Iso) complexIso (fun (r, i) =>
      if r < 10.0 && i < 10.0 then some (r * 2.0, i * 2.0) else none
    ) c
    ensureEq "traverse with Option" (some (Complex.mk 6.0 8.0)) result
}

def cases : List TestCase := [
    case_iso_view,
    case_iso_over,
    case_iso_set,
    case_iso_preview,
    case_iso_review,
    case_iso_traverse,
  ]

end IsoTests

/-! ## Section 2: Lens Tests -/
namespace LensTests

/-- Lens focusing on first element of pair -/
private def fstLens : Collimator.Lens' (Int × String) Int :=
  lens' (fun p => p.1) (fun p (v : Int) => (v, p.2))

private def case_lens_view : TestCase := {
  name := "Poly: Lens supports view",
  run := do
    let pair := (42, "hello")
    let n := view (optic := fun s a => Lens s s a a) fstLens pair
    ensureEq "view extracts first" 42 n
}

private def case_lens_over : TestCase := {
  name := "Poly: Lens supports over",
  run := do
    let pair := (42, "hello")
    let pair' := over (optic := Lens) fstLens (· + 1) pair
    ensureEq "over modifies first" (43, "hello") pair'
}

private def case_lens_set : TestCase := {
  name := "Poly: Lens supports set",
  run := do
    let pair := (42, "hello")
    let pair' := set (optic := Lens) fstLens 100 pair
    ensureEq "set replaces first" (100, "hello") pair'
}

private def case_lens_preview : TestCase := {
  name := "Poly: Lens supports preview (always succeeds)",
  run := do
    let pair := (42, "hello")
    let result := preview (optic := fun s a => Lens s s a a) fstLens pair
    ensureEq "preview succeeds" (some 42) result
}

private def case_lens_traverse : TestCase := {
  name := "Poly: Lens supports traverse",
  run := do
    let pair := (5, "hello")
    -- Traverse with Option (double if < 10)
    let result := traverse (optic := Lens) fstLens (fun n => if n < 10 then some (n * 2) else none) pair
    ensureEq "traverse with Option" (some (10, "hello")) result
}

def cases : List TestCase := [
    case_lens_view,
    case_lens_over,
    case_lens_set,
    case_lens_preview,
    case_lens_traverse,
  ]

end LensTests

/-! ## Section 3: Prism Tests -/
namespace PrismTests

private def case_prism_preview : TestCase := {
  name := "Poly: Prism supports preview",
  run := do
    let opt1 : Option Int := some 42
    let opt2 : Option Int := none
    let result1 := preview (optic := fun s a => Prism s s a a) somePrism opt1
    let result2 := preview (optic := fun s a => Prism s s a a) somePrism opt2
    ensureEq "preview some succeeds" (some 42) result1
    ensureEq "preview none fails" none result2
}

private def case_prism_review : TestCase := {
  name := "Poly: Prism supports review",
  run := do
    let opt : Option Int := review (optic := Prism) (somePrism (α := Int) (β := Int)) 42
    ensureEq "review constructs" (some 42) opt
}

private def case_prism_over : TestCase := {
  name := "Poly: Prism supports over",
  run := do
    let opt1 : Option Int := some 42
    let opt2 : Option Int := none
    let result1 := over (optic := Prism) (somePrism (α := Int) (β := Int)) (· + 1) opt1
    let result2 := over (optic := Prism) (somePrism (α := Int) (β := Int)) (· + 1) opt2
    ensureEq "over some modifies" (some 43) result1
    ensureEq "over none preserves" none result2
}

private def case_prism_set : TestCase := {
  name := "Poly: Prism supports set",
  run := do
    let opt : Option Int := some 42
    let result := set (optic := Prism) (somePrism (α := Int) (β := Int)) 100 opt
    ensureEq "set replaces" (some 100) result
}

private def case_prism_traverse : TestCase := {
  name := "Poly: Prism supports traverse",
  run := do
    let opt1 : Option Int := some 5
    let opt2 : Option Int := none
    -- Traverse with Option (double if < 10)
    let result1 := traverse (optic := Prism) (somePrism (α := Int) (β := Int)) (fun n => if n < 10 then some (n * 2) else none) opt1
    let result2 := traverse (optic := Prism) (somePrism (α := Int) (β := Int)) (fun n => if n < 10 then some (n * 2) else none) opt2
    ensureEq "traverse some" (some (some 10)) result1
    ensureEq "traverse none" (some none) result2
}

def cases : List TestCase := [
  case_prism_preview,
  case_prism_review,
  case_prism_over,
  case_prism_set,
  case_prism_traverse
]

end PrismTests

/-! ## Section 4: Traversal Tests -/
namespace TraversalTests

private def case_traversal_over : TestCase := {
  name := "Poly: Traversal supports over",
  run := do
    let list := [1, 2, 3]
    let result := over (optic := Traversal) eachList (· + 1) list
    ensureEq "over increments all" [2, 3, 4] result
}

private def case_traversal_set : TestCase := {
  name := "Poly: Traversal supports set",
  run := do
    let list := [1, 2, 3]
    let result := set (optic := Traversal) eachList 0 list
    ensureEq "set replaces all" [0, 0, 0] result
}

private def case_traversal_traverse : TestCase := {
  name := "Poly: Traversal supports traverse",
  run := do
    let list := [1, 2, 3]
    -- Traverse with Option (all elements double if < 5)
    let result : Option (List Int) := traverse (optic := Traversal) eachList (fun n => if n < 5 then some (n * 2) else none) list
    ensureEq "traverse all succeed" (some [2, 4, 6]) result

    let list2 := [1, 10, 3]
    let result2 : Option (List Int) := traverse (optic := Traversal) eachList (fun n => if n < 5 then some (n * 2) else none) list2
    ensureEq "traverse one fails" none result2
}

def cases : List TestCase := [
  case_traversal_over,
  case_traversal_set,
  case_traversal_traverse
]

end TraversalTests

/-! ## Section 5: AffineTraversal Tests -/
namespace AffineTests

/-- AffineTraversal from Prism -/
private def someAffine : Collimator.AffineTraversal' (Option Int) Int :=
  ofPrism (somePrism (α := Int) (β := Int))

private def case_affine_preview : TestCase := {
  name := "Poly: AffineTraversal supports preview",
  run := do
    let opt1 : Option Int := some 42
    let opt2 : Option Int := none
    let result1 := preview (optic := fun s a => AffineTraversal s s a a) someAffine opt1
    let result2 := preview (optic := fun s a => AffineTraversal s s a a) someAffine opt2
    ensureEq "preview some succeeds" (some 42) result1
    ensureEq "preview none fails" none result2
}

private def case_affine_over : TestCase := {
  name := "Poly: AffineTraversal supports over",
  run := do
    let opt1 : Option Int := some 42
    let opt2 : Option Int := none
    let result1 := over (optic := AffineTraversal) someAffine (· + 1) opt1
    let result2 := over (optic := AffineTraversal) someAffine (· + 1) opt2
    ensureEq "over some modifies" (some 43) result1
    ensureEq "over none preserves" none result2
}

private def case_affine_set : TestCase := {
  name := "Poly: AffineTraversal supports set",
  run := do
    let opt : Option Int := some 42
    let result := set (optic := AffineTraversal) someAffine 100 opt
    ensureEq "set replaces" (some 100) result
}

private def case_affine_traverse : TestCase := {
  name := "Poly: AffineTraversal supports traverse",
  run := do
    let opt1 : Option Int := some 5
    let opt2 : Option Int := none
    -- Traverse with Option (double if < 10)
    let result1 := traverse (optic := AffineTraversal) someAffine (fun n => if n < 10 then some (n * 2) else none) opt1
    let result2 := traverse (optic := AffineTraversal) someAffine (fun n => if n < 10 then some (n * 2) else none) opt2
    ensureEq "traverse some" (some (some 10)) result1
    ensureEq "traverse none" (some none) result2
}

def cases : List TestCase := [
  case_affine_preview,
  case_affine_over,
  case_affine_set,
  case_affine_traverse
]

end AffineTests

/-! ## Section 6: Polymorphic Functions -/
namespace PolymorphicTests

/-- Test lens for polymorphic examples -/
private def testFstLens : Collimator.Lens' (Int × String) Int :=
  lens' (fun p => p.1) (fun p v => (v, p.2))

/-- Test iso for polymorphic examples -/
private def testComplexIso : Collimator.Iso Complex Complex (Float × Float) (Float × Float) :=
  iso
    (forward := fun c => (c.real, c.imag))
    (back := fun (r, i) => { real := r, imag := i })

/-- Polymorphic increment: works with any optic supporting over -/
def incrementLens {s t : Type} (o : Lens s t Int Int) : s → t :=
  over (optic := Lens) o (· + 1)

def incrementPrism {s t : Type} (o : Prism s t Int Int) : s → t :=
  over (optic := Prism) o (· + 1)

def incrementTraversal {s t : Type} (o : Traversal s t Int Int) : s → t :=
  over (optic := Traversal) o (· + 1)

private def case_polymorphic_increment : TestCase := {
  name := "Poly: Polymorphic increment works across optic types",
  run := do
    -- Works with Lens
    let pair := (42, "hello")
    let pair' := incrementLens testFstLens pair
    ensureEq "increment via lens" (43, "hello") pair'

    -- Works with Prism
    let opt : Option Int := some 42
    let opt' := incrementPrism (somePrism (α := Int) (β := Int)) opt
    ensureEq "increment via prism" (some 43) opt'

    -- Works with Traversal
    let list := [1, 2, 3]
    let list' := incrementTraversal eachList list
    ensureEq "increment via traversal" [2, 3, 4] list'
}

/-- Polymorphic viewer: works with any optic supporting view -/
def getValueLens {s a : Type} (o : Lens s s a a) (x : s) : a :=
  view (optic := fun s a => Lens s s a a) o x

def getValueIso {s a : Type} (o : Iso s s a a) (x : s) : a :=
  view (optic := fun s a => Iso s s a a) o x

private def case_polymorphic_view : TestCase := {
  name := "Poly: Polymorphic view works across optic types",
  run := do
    -- Works with Lens
    let pair := (42, "hello")
    let n := getValueLens testFstLens pair
    ensureEq "view via lens" 42 n

    -- Works with Iso
    let c : Complex := { real := 3.0, imag := 4.0 }
    let tuple := getValueIso testComplexIso c
    ensureEq "view via iso" (3.0, 4.0) tuple
}

def cases : List TestCase := [
  case_polymorphic_increment,
  case_polymorphic_view
]

end PolymorphicTests

/-! ## Complete Test Suite -/

def cases : List TestCase :=
  IsoTests.cases ++
  LensTests.cases ++
  PrismTests.cases ++
  TraversalTests.cases ++
  AffineTests.cases ++
  PolymorphicTests.cases

end CollimatorTests.Poly
