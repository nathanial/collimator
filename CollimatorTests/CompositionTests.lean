import Batteries
import Collimator.Core
import Collimator.Optics
import Collimator.Combinators
import Collimator.Instances
import Collimator.Operators
import Collimator.Concrete.FunArrow
import Collimator.Concrete.Forget
import Crucible

/-!
# Composition Tests for Collimator Optics

Comprehensive tests for optics composition including:
- Edge cases and boundary conditions
- Deep compositions (3+ levels)
- Heterogeneous compositions (mixing different optic types)
- Recursive tree traversals
- Stress tests with large structures

This file consolidates tests from:
- CollimatorTests/EdgeCases.lean
- CollimatorTests/AdvancedShowcase/DeepComposition.lean
- CollimatorTests/AdvancedShowcase/HeterogeneousCompositions.lean
- CollimatorTests/AdvancedShowcase/MindBending.lean
- CollimatorTests/PropertyTests.lean (stress tests only)
-/

namespace CollimatorTests.CompositionTests

open Collimator
open Collimator.Core
open Collimator.Combinators
open Collimator.Instances
open Collimator.Instances.List
open Collimator.Instances.Prod
open Collimator.Instances.Option (somePrism somePrism')
open Collimator.Instances.Sum (left right left' right')
open Collimator.Fold (toList toListTraversal ofLens composeLensFold composeFold)
open Collimator.AffineTraversalOps (ofPrism)
open Crucible
open scoped Collimator.Operators
open scoped Collimator.Fold

testSuite "Composition Tests"

/-! ## Edge Case Tests -/

test "Edge: Traversal over empty list returns empty list" := do
  let tr : Traversal' (List Int) Int := Traversal.eachList
  let result := ([] : List Int) & tr %~ (· + 100)
  result ≡ ([] : List Int)

test "Edge: Fold over empty list returns empty" := do
  let tr : Traversal' (List Int) Int := Traversal.eachList
  let result := ([] : List Int) ^.. tr
  result ≡ ([] : List Int)

test "Edge: Traversal over none returns none" := do
  let tr : Traversal' (Option Int) Int := Traversal.eachOption
  let result := (none : Option Int) & tr %~ (· * 2)
  result ≡ (none : Option Int)

test "Edge: Prism preview returns none for non-matching" := do
  let p : Prism' (Sum Int String) Int := Collimator.Instances.Sum.left' (α := Int) (β := String)
  let result := Sum.inr "not an int" ^? p
  result ≡ (none : Option Int)

test "Edge: Affine traversal with no focus leaves unchanged" := do
  let prism : Prism' (Option Int) Int := Collimator.Instances.Option.somePrism' Int
  let aff : AffineTraversal' (Option Int) Int := AffineTraversalOps.ofPrism prism
  let result := (none : Option Int) & aff .~ 999
  result ≡ (none : Option Int)

test "Edge: Single element list traversal" := do
  let tr : Traversal' (List Int) Int := Traversal.eachList
  let result := [42] & tr %~ (· + 1)
  result ≡ [43]

test "Edge: Some value traversal" := do
  let tr : Traversal' (Option Int) Int := Traversal.eachOption
  let result := some 7 & tr %~ (· * 3)
  result ≡ (some 21)

test "Edge: 3-level lens composition" := do
  let nested : (((Int × Int) × Int) × Int) := (((1, 2), 3), 4)

  let l1 : Lens' ((((Int × Int) × Int) × Int)) (((Int × Int) × Int)) := _1
  let l2 : Lens' (((Int × Int) × Int)) ((Int × Int)) := _1
  let l3 : Lens' ((Int × Int)) Int := _1

  let composed : Lens' ((((Int × Int) × Int) × Int)) Int := l1 ∘ l2 ∘ l3

  (nested ^. composed) ≡ 1
  (nested & composed .~ 99) ≡ ((((99, 2), 3), 4))

test "Edge: 5-level lens composition" := do
  let nested : ((((Int × Int) × Int) × Int) × Int) := ((((1, 2), 3), 4), 5)

  let l1 : Lens' (((((Int × Int) × Int) × Int) × Int)) ((((Int × Int) × Int) × Int)) := _1
  let l2 : Lens' ((((Int × Int) × Int) × Int)) (((Int × Int) × Int)) := _1
  let l3 : Lens' (((Int × Int) × Int)) ((Int × Int)) := _1
  let l4 : Lens' ((Int × Int)) Int := _1

  let composed : Lens' (((((Int × Int) × Int) × Int) × Int)) Int := l1 ∘ l2 ∘ l3 ∘ l4

  (nested ^. composed) ≡ 1
  (nested & composed .~ 42) ≡ (((((42, 2), 3), 4), 5))

test "Edge: Lens ∘ Traversal composition" := do
  let pair : (List Int × String) := ([1, 2, 3], "hello")

  let lensToList : Lens' (List Int × String) (List Int) := _1
  let traverseList : Traversal' (List Int) Int := Traversal.eachList

  let composed : Traversal' (List Int × String) Int := lensToList ∘ traverseList

  let result := pair & composed %~ (· + 10)
  result ≡ (([11, 12, 13], "hello"))

test "Edge: Traversal ∘ Lens composition" := do
  let pairs : List (Int × String) := [(1, "a"), (2, "b"), (3, "c")]

  let traverseList : Traversal' (List (Int × String)) (Int × String) := Traversal.eachList
  let lensToFirst : Lens' (Int × String) Int := _1

  let composed : Traversal' (List (Int × String)) Int := traverseList ∘ lensToFirst

  let result := pairs & composed %~ (· * 2)
  result ≡ ([(2, "a"), (4, "b"), (6, "c")])

test "Edge: Lens ∘ Prism composition" := do
  let pair1 : (Option Int × String) := (some 42, "test")
  let pair2 : (Option Int × String) := (none, "test")

  let lensToOpt : Lens' (Option Int × String) (Option Int) := _1
  let prismToSome : Prism' (Option Int) Int := Collimator.Instances.Option.somePrism' Int

  let composed : AffineTraversal' (Option Int × String) Int := lensToOpt ∘ prismToSome

  let preview1 := pair1 ^? composed
  preview1 ≡? 42

  let preview2 := pair2 ^? composed
  preview2 ≡ (none : Option Int)

  let set1 := pair1 & composed .~ 99
  set1 ≡ ((some 99, "test"))

test "Edge: Identity lens" := do
  let idLens : Lens' Int Int := lens' id (fun _ x => x)

  (42 ^. idLens) ≡ 42
  (42 & idLens .~ 99) ≡ 99
  (42 & idLens %~ (· + 8)) ≡ 50

test "Edge: Constant lens behavior" := do
  let constLens : Lens' (Int × Int) Int := const 0

  let pair : (Int × Int) := (10, 20)

  (pair ^. constLens) ≡ 0
  (pair & constLens .~ 999) ≡ pair

test "Edge: Traverse with always-failing effect" := do
  let tr : Traversal' (List Int) Int := Traversal.eachList
  let alwaysFail : Int → Option Int := fun _ => none

  let result := Traversal.traverse' tr alwaysFail [1, 2, 3]
  result ≡ (none : Option (List Int))

test "Edge: Traverse with always-succeeding effect" := do
  let tr : Traversal' (List Int) Int := Traversal.eachList
  let alwaysSucceed : Int → Option Int := fun x => some (x + 1)

  let result := Traversal.traverse' tr alwaysSucceed [1, 2, 3]
  result ≡ (some [2, 3, 4])

test "Edge: Traverse empty list with failing effect succeeds" := do
  let tr : Traversal' (List Int) Int := Traversal.eachList
  let alwaysFail : Int → Option Int := fun _ => none

  let result := Traversal.traverse' tr alwaysFail []
  result ≡ (some [])

test "Edge: List index access at valid indices" := do
  let xs := [10, 20, 30, 40, 50]

  let first := xs[0]?
  let middle := xs[2]?
  let last := xs[4]?

  first ≡? 10
  middle ≡? 30
  last ≡? 50

test "Edge: List index access at invalid indices" := do
  let xs : List Int := [10, 20, 30]

  let tooLarge := xs[10]?
  let exactlyTooLarge := xs[3]?

  tooLarge ≡ (none : Option Int)
  exactlyTooLarge ≡ (none : Option Int)

/-! ## Deep Composition Tests -/

-- Custom data types for deep composition tests

structure Address where
  street : String
  city : String
  zipCode : String
  deriving BEq, Repr

structure Employee where
  name : String
  address : Address
  salary : Int
  deriving BEq, Repr

structure Department where
  name : String
  employees : List Employee
  deriving BEq, Repr

structure Company where
  name : String
  departments : List Department
  deriving BEq, Repr

structure CompanyWithCEO where
  name : String
  departments : List Department
  ceo : Option Employee
  deriving BEq, Repr

-- Field lenses
private def Address.streetLens : Lens' Address String := fieldLens% Address street
private def Address.cityLens : Lens' Address String := fieldLens% Address city
private def Address.zipCodeLens : Lens' Address String := fieldLens% Address zipCode

private def Employee.nameLens : Lens' Employee String := fieldLens% Employee name
private def Employee.addressLens : Lens' Employee Address := fieldLens% Employee address
private def Employee.salaryLens : Lens' Employee Int := fieldLens% Employee salary

private def Department.nameLens : Lens' Department String := fieldLens% Department name
private def Department.employeesLens : Lens' Department (List Employee) := fieldLens% Department employees

private def Company.nameLens : Lens' Company String := fieldLens% Company name
private def Company.departmentsLens : Lens' Company (List Department) := fieldLens% Company departments

private def CompanyWithCEO.nameLens : Lens' CompanyWithCEO String := fieldLens% CompanyWithCEO name
private def CompanyWithCEO.departmentsLens : Lens' CompanyWithCEO (List Department) := fieldLens% CompanyWithCEO departments
private def CompanyWithCEO.ceoLens : Lens' CompanyWithCEO (Option Employee) := fieldLens% CompanyWithCEO ceo

-- Isomorphisms
private def stringToListIso : Iso String String (List Char) (List Char) :=
  iso
    (forward := String.toList)
    (back := String.ofList)

-- Inhabited instances
private instance : Inhabited Department where
  default := { name := "", employees := [] }

private instance : Inhabited Employee where
  default := { name := "", address := { street := "", city := "", zipCode := "" }, salary := 0 }

-- Helper lens
private def headLens {α : Type} [Inhabited α] : Lens' (List α) α :=
  lens'
    (fun xs => xs.head!)
    (fun xs new => match xs with
      | [] => [new]
      | _ :: tail => new :: tail)

test "Deep: Nested tuples _1 . _2 composition" := do
    let data : ((Int × String) × Float) := ((42, "hello"), 3.14)

    let lens1 : Lens ((Int × String) × Float) ((Int × String) × Float) (Int × String) (Int × String) := _1
    let lens2 : Lens (Int × String) (Int × String) String String := _2
    let composed : Lens ((Int × String) × Float) ((Int × String) × Float) String String :=
      lens1 ∘ lens2

    let str := data ^. composed
    str ≡ "hello"

    let modified := data & composed %~ (· ++ "!")
    let expected := ((42, "hello!"), 3.14)
    modified ≡ expected

    let updated := data & composed .~ "world"
    let expected2 := ((42, "world"), 3.14)
    updated ≡ expected2

test "Deep: Company → Dept → Employee → Address → Zip (5-level chain)" := do
    let address : Address := {
      street := "123 Main St",
      city := "Springfield",
      zipCode := "12345"
    }

    let employee : Employee := {
      name := "Alice",
      address := address,
      salary := 75000
    }

    let department : Department := {
      name := "Engineering",
      employees := [employee]
    }

    let company : Company := {
      name := "Acme Corp",
      departments := [department]
    }

    let companyToZip : Lens' Company String :=
      Company.departmentsLens ∘ headLens (α := Department) ∘ Department.employeesLens ∘
      headLens (α := Employee) ∘ Employee.addressLens ∘ Address.zipCodeLens

    let zip := company ^. companyToZip
    zip ≡ "12345"

    let modified := company & companyToZip %~ (fun _ => "99999")
    let newZip := modified ^. companyToZip
    newZip ≡ "99999"

    modified.name ≡ "Acme Corp"
    modified.departments.head!.name ≡ "Engineering"
    modified.departments.head!.employees.head!.name ≡ "Alice"
    modified.departments.head!.employees.head!.address.city ≡ "Springfield"

    let updated := company & companyToZip .~ "54321"
    let finalZip := updated ^. companyToZip
    finalZip ≡ "54321"

test "Deep: Iso ∘ Traversal (String → List Char transformations)" := do
    let s : String := "hello"

    let stringCharsTraversal : Traversal String String Char Char :=
      stringToListIso ∘ traversed (α := Char) (β := Char)

    let chars := s ^.. stringCharsTraversal
    chars ≡ ['h', 'e', 'l', 'l', 'o']

    let upper := s & stringCharsTraversal %~ Char.toUpper
    upper ≡ "HELLO"

    let exclaimed := s & stringCharsTraversal %~ (fun c => if c == 'l' then '!' else c)
    exclaimed ≡ "he!!o"

    let empty := ""
    let emptyChars := empty ^.. stringCharsTraversal
    emptyChars ≡ ([] : List Char)

test "Deep: Traversal ∘ Prism ∘ Lens (Skip None, process Some)" := do
    let emp1 : Employee := {
      name := "Alice",
      address := { street := "1 Main St", city := "NYC", zipCode := "10001" },
      salary := 100000
    }
    let emp2 : Employee := {
      name := "Bob",
      address := { street := "2 Oak Ave", city := "LA", zipCode := "90001" },
      salary := 110000
    }
    let emp3 : Employee := {
      name := "Carol",
      address := { street := "3 Pine Rd", city := "SF", zipCode := "94101" },
      salary := 120000
    }

    let employees : List (Option Employee) := [
      some emp1,
      none,
      some emp2,
      none,
      none,
      some emp3
    ]

    let finalTraversal := optic%
      traversed ∘ somePrism' Employee ∘ Employee.addressLens ∘ Address.cityLens
      : Traversal' (List (Option Employee)) String

    let cities := employees ^.. finalTraversal
    cities ≡ ["NYC", "LA", "SF"]

    let remote : List (Option Employee) := employees & finalTraversal %~ (fun _ => "Remote")
    let remoteCities := remote ^.. finalTraversal
    remoteCities ≡ ["Remote", "Remote", "Remote"]

    remote.length ≡ 6

    match remote.head! with
    | some e => e.address.city ≡ "Remote"
    | none => ensure false "Expected Some employee at index 0"

    match remote[1]! with
    | none => pure ()
    | some _ => ensure false "Expected None at index 1"

test "Deep: Traversal ∘ Prism with Sum (Skip Left errors, process Right values)" := do
    let emp1 : Employee := {
      name := "Alice",
      address := { street := "1 Main", city := "NYC", zipCode := "10001" },
      salary := 100000
    }
    let emp2 : Employee := {
      name := "Bob",
      address := { street := "2 Oak", city := "LA", zipCode := "90001" },
      salary := 110000
    }

    let results : List (Sum String Employee) := [
      Sum.inr emp1,
      Sum.inl "Error: Employee not found",
      Sum.inr emp2,
      Sum.inl "Error: Invalid data",
      Sum.inl "Error: Permission denied"
    ]

    let finalTraversal := optic%
      traversed ∘ right' String Employee ∘ Employee.salaryLens
      : Traversal' (List (Sum String Employee)) Int

    let salaries := results ^.. finalTraversal
    salaries ≡ [100000, 110000]

    let raised : List (Sum String Employee) := results & finalTraversal %~ (fun s => s + s / 10)
    let newSalaries := raised ^.. finalTraversal
    newSalaries ≡ [110000, 121000]

    match raised[1]? with
    | some (Sum.inl msg) => msg ≡ "Error: Employee not found"
    | some (Sum.inr _) => ensure false "Expected error at index 1"
    | none => ensure false "Expected element at index 1"

test "Deep: AffineTraversal for safe head access" := do
    let emp1 : Employee := {
      name := "Alice",
      address := { street := "1 Main", city := "NYC", zipCode := "10001" },
      salary := 100000
    }
    let emp2 : Employee := {
      name := "Bob",
      address := { street := "2 Oak", city := "LA", zipCode := "90001" },
      salary := 110000
    }

    let employees : List Employee := [emp1, emp2]
    let empty : List Employee := []

    let headLens : Lens' (List Employee) (Option Employee) := Collimator.Indexed.HasAt.focus 0

    let finalAffine : AffineTraversal' (List Employee) String :=
      headLens ∘
      ofPrism (somePrism' Employee) ∘
      Employee.addressLens ∘
      Address.cityLens

    let city := employees ^? finalAffine
    city ≡ (some "NYC")

    let noCity := empty ^? finalAffine
    noCity ≡ (none : Option String)

    let modified : List Employee := employees & finalAffine %~ (fun _ => "SF")
    let newCity := modified ^? finalAffine
    newCity ≡ (some "SF")

    match modified.tail? with
    | some tail =>
        match tail.head? with
        | some emp => emp.address.city ≡ "LA"
        | none => ensure false "Expected second employee"
    | none => ensure false "Expected tail"

    let stillEmpty : List Employee := empty & finalAffine .~ "Denver"
    stillEmpty ≡ empty

test "Deep: AffineTraversal with List.at for safe indexed access" := do
    let emp1 : Employee := {
      name := "Alice",
      address := { street := "1 Main", city := "NYC", zipCode := "10001" },
      salary := 100000
    }
    let emp2 : Employee := {
      name := "Bob",
      address := { street := "2 Oak", city := "LA", zipCode := "90001" },
      salary := 110000
    }
    let emp3 : Employee := {
      name := "Carol",
      address := { street := "3 Pine", city := "SF", zipCode := "94101" },
      salary := 120000
    }

    let employees := [emp1, emp2, emp3]

    let atLens : Lens' (List Employee) (Option Employee) := Collimator.Indexed.HasAt.focus 1

    let finalAffine := optic%
      atLens ∘ ofPrism (somePrism' Employee) ∘ Employee.salaryLens
      : AffineTraversal' (List Employee) Int

    let salary := employees ^? finalAffine
    salary ≡ (some 110000)

    let raised : List Employee := employees & finalAffine %~ (· + 10000)
    let newSalary := raised ^? finalAffine
    newSalary ≡ (some 120000)

    match raised.head? with
    | some e => e.salary ≡ 100000
    | none => ensure false "Expected first employee"

    let atLens10 : Lens' (List Employee) (Option Employee) := Collimator.Indexed.HasAt.focus 10
    let outOfBounds := optic%
      atLens10 ∘ ofPrism (somePrism' Employee)
      : AffineTraversal' (List Employee) Employee

    let noEmployee := employees ^? outOfBounds
    noEmployee ≡ (none : Option Employee)

    let unchanged : List Employee := employees & outOfBounds %~ (fun e => { e with salary := 0 })
    unchanged ≡ employees

test "Deep: Fold for read-only access and multi-element aggregation" := do
    let eng1 : Employee := {
      name := "Alice",
      address := { street := "123 Main", city := "NYC", zipCode := "10001" },
      salary := 100000
    }
    let eng2 : Employee := {
      name := "Bob",
      address := { street := "456 Oak", city := "SF", zipCode := "94102" },
      salary := 110000
    }
    let sales1 : Employee := {
      name := "Carol",
      address := { street := "789 Pine", city := "LA", zipCode := "90001" },
      salary := 90000
    }
    let sales2 : Employee := {
      name := "Dave",
      address := { street := "321 Elm", city := "Austin", zipCode := "78701" },
      salary := 95000
    }
    let hr1 : Employee := {
      name := "Eve",
      address := { street := "654 Maple", city := "Boston", zipCode := "02101" },
      salary := 85000
    }

    let engineering : Department := { name := "Engineering", employees := [eng1, eng2] }
    let sales : Department := { name := "Sales", employees := [sales1, sales2] }
    let hr : Department := { name := "HR", employees := [hr1] }

    let company : Company := {
      name := "MegaCorp",
      departments := [engineering, sales, hr]
    }

    let companyToFirstCity : Lens' Company String := lens'
      (fun c => c.departments.head!.employees.head!.address.city)
      (fun c city' =>
        let d := c.departments.head!
        let e := d.employees.head!
        let a := e.address
        let a' := { a with city := city' }
        let e' := { e with address := a' }
        let d' := { d with employees := e' :: d.employees.tail! }
        { c with departments := d' :: c.departments.tail! })

    let firstCity := company ^. companyToFirstCity
    firstCity ≡ "NYC"

    let allZipsTraversal := optic%
      Company.departmentsLens ∘ traversed ∘ Department.employeesLens ∘ traversed ∘ Employee.addressLens ∘ Address.zipCodeLens
      : Traversal' Company String

    let allZipCodes : List String := company ^.. allZipsTraversal
    allZipCodes ≡ ["10001", "94102", "90001", "78701", "02101"]

    let allSalariesTraversal := optic%
      Company.departmentsLens ∘ traversed ∘ Department.employeesLens ∘ traversed ∘ Employee.salaryLens
      : Traversal' Company Int

    let allSalaries : List Int := company ^.. allSalariesTraversal
    allSalaries ≡ [100000, 110000, 90000, 95000, 85000]

    let totalSalary := allSalaries.foldl (· + ·) (0 : Int)
    totalSalary ≡ 480000

    let avgSalary := totalSalary / allSalaries.length
    avgSalary ≡ 96000

    let allEmployeesTraversal := optic%
      Company.departmentsLens ∘ traversed ∘ Department.employeesLens ∘ traversed
      : Traversal' Company Employee

    let allEmployees : List Employee := company ^.. allEmployeesTraversal
    let employeeCount := allEmployees.length
    employeeCount ≡ 5

    let allCitiesTraversal := optic%
      Company.departmentsLens ∘ traversed ∘ Department.employeesLens ∘ traversed ∘ Employee.addressLens ∘ Address.cityLens
      : Traversal' Company String

    let allCities := company ^.. allCitiesTraversal
    allCities ≡ ["NYC", "SF", "LA", "Austin", "Boston"]

    let uniqueCities := allCities.eraseDups
    uniqueCities.length ≡ 5

    let highEarners := allEmployees.filter (fun (e : Employee) => e.salary > 95000)
    highEarners.length ≡ 2
    (highEarners.map (fun (e : Employee) => e.name)) ≡ ["Alice", "Bob"]

test "Deep: Ultimate 6-optic composition (Lens ∘ Traversal ∘ Lens ∘ Iso ∘ Traversal ∘ filtered)" := do
    let emp1 : Employee := {
      name := "alice",
      address := { street := "1 Main", city := "NYC", zipCode := "10001" },
      salary := 100000
    }
    let emp2 : Employee := {
      name := "bob",
      address := { street := "2 Oak", city := "SF", zipCode := "94102" },
      salary := 110000
    }
    let emp3 : Employee := {
      name := "carol",
      address := { street := "3 Pine", city := "LA", zipCode := "90001" },
      salary := 90000
    }

    let engineering : Department := { name := "Engineering", employees := [emp1, emp2] }
    let sales : Department := { name := "Sales", employees := [emp3] }
    let company : Company := { name := "TechCorp", departments := [engineering, sales] }

    let nameCharsTraversal : Traversal' Employee Char :=
      Employee.nameLens ∘ (stringToListIso ∘ traversed (α := Char) (β := Char))

    let capitalized : Employee := emp1 & nameCharsTraversal %~ Char.toUpper
    capitalized.name ≡ "ALICE"

    let companyToAllNameChars := optic%
      Company.departmentsLens ∘ traversed ∘ Department.employeesLens ∘ traversed ∘
      Employee.nameLens ∘ stringToListIso ∘ traversed
      : Traversal' Company Char

    let allCaps : Company := company & companyToAllNameChars %~ Char.toUpper

    allCaps.departments[0]!.employees[0]!.name ≡ "ALICE"
    allCaps.departments[0]!.employees[1]!.name ≡ "BOB"
    allCaps.departments[1]!.employees[0]!.name ≡ "CAROL"

    let allChars := company ^.. companyToAllNameChars
    allChars ≡ ['a','l','i','c','e','b','o','b','c','a','r','o','l']

    let aCharsOnly : Traversal' Company Char :=
      Collimator.Combinators.filtered companyToAllNameChars (· == 'a')

    let countAs := (company ^.. aCharsOnly).length
    countAs ≡ 2

    let replacedAs : Company := company & aCharsOnly %~ (fun _ => 'A')
    replacedAs.departments[0]!.employees[0]!.name ≡ "Alice"
    replacedAs.departments[1]!.employees[0]!.name ≡ "cArol"

test "Deep: Nested Options - Lens ∘ Prism ∘ Lens with short-circuit" := do
    let ceoEmployee : Employee := {
      name := "Alice",
      address := { street := "1 Executive Blvd", city := "NYC", zipCode := "10001" },
      salary := 500000
    }

    let eng1 : Employee := {
      name := "Bob",
      address := { street := "2 Main", city := "SF", zipCode := "94102" },
      salary := 120000
    }
    let engineering : Department := { name := "Engineering", employees := [eng1] }

    let companyWithCEO : CompanyWithCEO := {
      name := "TechCorp",
      departments := [engineering],
      ceo := some ceoEmployee
    }

    let companyNoCEO : CompanyWithCEO := {
      name := "StartupCo",
      departments := [engineering],
      ceo := none
    }

    let ceoToCity : AffineTraversal' CompanyWithCEO String :=
      CompanyWithCEO.ceoLens ∘
      ofPrism (somePrism' Employee) ∘
      Employee.addressLens ∘
      Address.cityLens

    let cityWithCEO := companyWithCEO ^? ceoToCity
    cityWithCEO ≡ (some "NYC")

    let cityNoCEO := companyNoCEO ^? ceoToCity
    cityNoCEO ≡ (none : Option String)

    let movedCEO : CompanyWithCEO := companyWithCEO & ceoToCity .~ "Boston"
    let newCity := movedCEO ^? ceoToCity
    newCity ≡ (some "Boston")

    match movedCEO.ceo with
    | some emp => emp.name ≡ "Alice"
    | none => ensure false "Expected CEO to exist"

    let unchangedNoCEO : CompanyWithCEO := companyNoCEO & ceoToCity .~ "Boston"
    unchangedNoCEO ≡ companyNoCEO

    let upperNoCEO : CompanyWithCEO := companyNoCEO & ceoToCity %~ String.toUpper
    upperNoCEO ≡ companyNoCEO

    let ceoToStreet : AffineTraversal' CompanyWithCEO String :=
      CompanyWithCEO.ceoLens ∘
      ofPrism (somePrism' Employee) ∘
      Employee.addressLens ∘
      Address.streetLens

    let street := companyWithCEO ^? ceoToStreet
    street ≡ (some "1 Executive Blvd")

    let noStreet := companyNoCEO ^? ceoToStreet
    noStreet ≡ (none : Option String)

test "Deep: Company → all Depts → all Employees → salary (Lens + Traversal mix)" := do
    let eng1 : Employee := { name := "Alice", address := { street := "1 Main", city := "NYC", zipCode := "10001" }, salary := 100000 }
    let eng2 : Employee := { name := "Bob", address := { street := "2 Main", city := "NYC", zipCode := "10002" }, salary := 110000 }
    let sales1 : Employee := { name := "Carol", address := { street := "3 Main", city := "LA", zipCode := "90001" }, salary := 90000 }
    let sales2 : Employee := { name := "Dave", address := { street := "4 Main", city := "LA", zipCode := "90002" }, salary := 95000 }

    let engineering : Department := { name := "Engineering", employees := [eng1, eng2] }
    let sales : Department := { name := "Sales", employees := [sales1, sales2] }

    let company : Company := { name := "TechCorp", departments := [engineering, sales] }

    let companyToAllSalaries := optic%
      Company.departmentsLens ∘ traversed ∘ Department.employeesLens ∘ traversed ∘ Employee.salaryLens
      : Traversal' Company Int

    let allSalaries : List Int := company ^.. companyToAllSalaries
    allSalaries ≡ [100000, 110000, 90000, 95000]

    let raised : Company := company & companyToAllSalaries %~ (fun sal => sal + (sal / 10))
    let newSalaries : List Int := raised ^.. companyToAllSalaries
    newSalaries ≡ [110000, 121000, 99000, 104500]

    raised.name ≡ "TechCorp"

    raised.departments.length ≡ 2
    raised.departments.head!.name ≡ "Engineering"

    raised.departments.head!.employees.head!.name ≡ "Alice"
    raised.departments.head!.employees.tail!.head!.name ≡ "Bob"

    let normalized : Company := company & companyToAllSalaries .~ 100000
    let finalSalaries : List Int := normalized ^.. companyToAllSalaries
    finalSalaries ≡ [100000, 100000, 100000, 100000]

/-! ## Heterogeneous Composition Tests -/

-- Data structures for heterogeneous composition tests

private inductive Contact where
  | email : String → Contact
  | phone : String → Contact
  | none : Contact
  deriving BEq, Repr, Inhabited

private structure HetEmployee where
  name : String
  salary : Nat
  contact : Contact
  deriving BEq, Repr, Inhabited

private structure Project where
  title : String
  budget : Nat
  employees : List HetEmployee
  deriving BEq, Repr, Inhabited

private structure HetDepartment where
  name : String
  projects : List Project
  deriving BEq, Repr, Inhabited

private structure HetCompany where
  name : String
  departments : List HetDepartment
  deriving BEq, Repr, Inhabited

private inductive HetAddress where
  | domestic : String → String → HetAddress
  | international : String → String → String → HetAddress
  deriving BEq, Repr, Inhabited

private structure Person where
  name : String
  age : Nat
  address : Option HetAddress
  deriving BEq, Repr, Inhabited

private structure Team where
  name : String
  members : List Person
  deriving BEq, Repr, Inhabited

-- Lenses
private def salaryLens : Lens' HetEmployee Nat := fieldLens% HetEmployee salary
private def contactLens : Lens' HetEmployee Contact := fieldLens% HetEmployee contact
private def employeesLens : Lens' Project (List HetEmployee) := fieldLens% Project employees
private def budgetLens : Lens' Project Nat := fieldLens% Project budget
private def projectsLens : Lens' HetDepartment (List Project) := fieldLens% HetDepartment projects
private def departmentsLens : Lens' HetCompany (List HetDepartment) := fieldLens% HetCompany departments
private def addressLens : Lens' Person (Option HetAddress) := fieldLens% Person address
private def ageLens : Lens' Person Nat := fieldLens% Person age
private def membersLens : Lens' Team (List Person) := fieldLens% Team members

-- Prisms
private def emailPrism : Prism' Contact String := ctorPrism% Contact.email
private def phonePrism : Prism' Contact String := ctorPrism% Contact.phone

private def somePrismHet {α : Type} : Prism' (Option α) α :=
  prism (fun a => some a)
        (fun o => match o with
         | some a => Sum.inr a
         | none => Sum.inl none)

private def domesticPrism : Prism' HetAddress (String × String) := ctorPrism% HetAddress.domestic
private def internationalPrism : Prism' HetAddress (String × String × String) := ctorPrism% HetAddress.international

test "Het: Lens ∘ Traversal compositions" := do
    let project := Project.mk "App Rewrite" 100000 [
      HetEmployee.mk "Alice" 80000 (Contact.email "alice@example.com"),
      HetEmployee.mk "Bob" 75000 (Contact.phone "555-1234"),
      HetEmployee.mk "Carol" 90000 Contact.none
    ]

    let raiseComposed := optic% employeesLens ∘ List.traversed ∘ salaryLens : Traversal' Project Nat
    let afterRaise : Project := project & raiseComposed %~ (fun s => s * 110 / 100)

    afterRaise.employees[0]!.salary ≡ 88000
    afterRaise.employees[1]!.salary ≡ 82500
    afterRaise.employees[2]!.salary ≡ 99000

    let contactComposed := optic% employeesLens ∘ List.traversed ∘ contactLens : Traversal' Project Contact
    let noContact : Project := project & contactComposed %~ (fun _ => Contact.none)

    shouldSatisfy (noContact.employees.all (fun e => e.contact == Contact.none))
      "all contacts to be none"

test "Het: Traversal ∘ Prism compositions" := do
    let employees := [
      HetEmployee.mk "Alice" 80000 (Contact.email "alice@example.com"),
      HetEmployee.mk "Bob" 75000 (Contact.phone "555-1234"),
      HetEmployee.mk "Carol" 90000 (Contact.email "carol@company.org"),
      HetEmployee.mk "Dave" 85000 Contact.none
    ]

    let emailComposed := optic% List.traversed ∘ contactLens ∘ emailPrism : Traversal' (List HetEmployee) String
    let updated : List HetEmployee := employees & emailComposed %~
      (fun (email : String) => email.replace "@example.com" "@newdomain.com")

    match updated[0]!.contact with
    | Contact.email e => e ≡ "alice@newdomain.com"
    | _ => throw (IO.userError "Expected email contact")

    updated[1]!.contact ≡ Contact.phone "555-1234"

    match updated[2]!.contact with
    | Contact.email e => e ≡ "carol@company.org"
    | _ => throw (IO.userError "Expected email contact")

    let phoneComposed := optic% List.traversed ∘ contactLens ∘ phonePrism : Traversal' (List HetEmployee) String
    let phones : List HetEmployee := employees & phoneComposed %~ (fun p => "PHONE:" ++ p)

    match phones[1]!.contact with
    | Contact.phone p => p ≡ "PHONE:555-1234"
    | _ => throw (IO.userError "Expected phone contact")

test "Het: Lens ∘ Prism ∘ Lens chains" := do
    let team := Team.mk "Engineering" [
      Person.mk "Alice" 30 (some (HetAddress.domestic "123 Main St" "Boston")),
      Person.mk "Bob" 35 (some (HetAddress.international "456 High St" "London" "UK")),
      Person.mk "Carol" 28 none,
      Person.mk "Dave" 32 (some (HetAddress.domestic "789 Oak Ave" "Seattle"))
    ]

    let domesticAddressComposed := optic%
      membersLens ∘ List.traversed ∘ addressLens ∘ somePrismHet ∘ domesticPrism
      : Traversal' Team (String × String)

    let withCountry : Team := team & domesticAddressComposed %~
      (fun (pair : String × String) => (pair.1, pair.2 ++ ", USA"))

    match withCountry.members[0]!.address with
    | some (HetAddress.domestic s c) =>
        s ≡ "123 Main St"
        c ≡ "Boston, USA"
    | _ => throw (IO.userError "Expected domestic address")

    match withCountry.members[1]!.address with
    | some (HetAddress.international _ c _) =>
        c ≡ "London"
    | _ => throw (IO.userError "Expected international address")

    shouldBeNone withCountry.members[2]!.address

    match withCountry.members[3]!.address with
    | some (HetAddress.domestic s c) =>
        s ≡ "789 Oak Ave"
        c ≡ "Seattle, USA"
    | _ => throw (IO.userError "Expected domestic address")

test "Het: Deep heterogeneous chains (5-level traversal)" := do
    let company := HetCompany.mk "TechCorp" [
      HetDepartment.mk "Engineering" [
        Project.mk "Backend" 500000 [
          HetEmployee.mk "Alice" 100000 (Contact.email "alice@tech.com"),
          HetEmployee.mk "Bob" 95000 (Contact.phone "555-0001")
        ],
        Project.mk "Frontend" 400000 [
          HetEmployee.mk "Carol" 105000 (Contact.email "carol@tech.com"),
          HetEmployee.mk "Dave" 90000 Contact.none
        ]
      ],
      HetDepartment.mk "Sales" [
        Project.mk "Enterprise" 300000 [
          HetEmployee.mk "Eve" 85000 (Contact.email "eve@tech.com"),
          HetEmployee.mk "Frank" 80000 (Contact.phone "555-0002")
        ]
      ]
    ]

    let allSalariesComposed := optic%
      departmentsLens ∘ List.traversed ∘
      projectsLens ∘ List.traversed ∘
      employeesLens ∘ List.traversed ∘
      salaryLens
      : Traversal' HetCompany Nat

    let afterRaise : HetCompany := company & allSalariesComposed %~ (fun s => s * 115 / 100)

    let alice := afterRaise.departments[0]!.projects[0]!.employees[0]!
    alice.salary ≡ 115000

    let carol := afterRaise.departments[0]!.projects[1]!.employees[0]!
    carol.salary ≡ 120750

    let eve := afterRaise.departments[1]!.projects[0]!.employees[0]!
    eve.salary ≡ 97750

    let highBudgetEmails := optic%
      departmentsLens ∘ List.traversed ∘
      projectsLens ∘ filtered List.traversed (fun p => p.budget >= 400000) ∘
      employeesLens ∘ List.traversed ∘
      contactLens ∘ emailPrism
      : Traversal' HetCompany String

    let updated : HetCompany := company & highBudgetEmails %~
      (fun (email : String) => email.replace "@tech.com" "@techcorp.com")

    match updated.departments[0]!.projects[0]!.employees[0]!.contact with
    | Contact.email e => e ≡ "alice@techcorp.com"
    | _ => throw (IO.userError "Expected email contact")

    match updated.departments[0]!.projects[1]!.employees[0]!.contact with
    | Contact.email e => e ≡ "carol@techcorp.com"
    | _ => throw (IO.userError "Expected email contact")

    match updated.departments[1]!.projects[0]!.employees[0]!.contact with
    | Contact.email e => e ≡ "eve@tech.com"
    | _ => throw (IO.userError "Expected email contact")

    updated.departments[0]!.projects[0]!.employees[1]!.contact ≡
      Contact.phone "555-0001"

test "Het: Type inference across compositions" := do
    let project := Project.mk "Test" 100000 [
      HetEmployee.mk "Alice" 80000 (Contact.email "alice@test.com"),
      HetEmployee.mk "Bob" 75000 (Contact.phone "555-1234")
    ]

    let composed1 := optic% employeesLens ∘ List.traversed ∘ salaryLens : Traversal' Project Nat
    let result1 : Project := project & composed1 %~ (· + 5000)
    result1.employees[0]!.salary ≡ 85000

    let composed2 := optic% employeesLens ∘ List.traversed ∘ contactLens ∘ emailPrism : Traversal' Project String
    let result2 : Project := project & composed2 %~ (fun (s : String) => s ++ " (work)")

    match result2.employees[0]!.contact with
    | Contact.email e => e ≡ "alice@test.com (work)"
    | _ => throw (IO.userError "Expected email contact")

test "Het: Real-world scenario - company reorganization" := do
    let company := HetCompany.mk "StartupInc" [
      HetDepartment.mk "Product" [
        Project.mk "MVP" 200000 [
          HetEmployee.mk "Alice" 90000 (Contact.email "alice@startup.com"),
          HetEmployee.mk "Bob" 85000 (Contact.email "bob@startup.com"),
          HetEmployee.mk "Carol" 95000 (Contact.phone "555-0001")
        ]
      ],
      HetDepartment.mk "Growth" [
        Project.mk "Marketing" 150000 [
          HetEmployee.mk "Dave" 80000 (Contact.email "dave@startup.com"),
          HetEmployee.mk "Eve" 75000 Contact.none
        ]
      ]
    ]

    let allSalaries := optic%
      departmentsLens ∘ List.traversed ∘
      projectsLens ∘ List.traversed ∘
      employeesLens ∘ List.traversed ∘
      salaryLens
      : Traversal' HetCompany Nat
    let afterRaises : HetCompany := company & allSalaries %~ (fun s => s * 120 / 100)

    let allEmails := optic%
      departmentsLens ∘ List.traversed ∘
      projectsLens ∘ List.traversed ∘
      employeesLens ∘ List.traversed ∘
      contactLens ∘ emailPrism
      : Traversal' HetCompany String
    let newDomain : HetCompany := afterRaises & allEmails %~
                     (fun (e : String) => e.replace "@startup.com" "@bigcorp.com")

    let allBudgets := optic%
      departmentsLens ∘ List.traversed ∘
      projectsLens ∘ List.traversed ∘
      budgetLens
      : Traversal' HetCompany Nat
    let final : HetCompany := newDomain & allBudgets %~ (· * 2)

    let alice := final.departments[0]!.projects[0]!.employees[0]!
    alice.salary ≡ 108000
    match alice.contact with
    | Contact.email e => e ≡ "alice@bigcorp.com"
    | _ => throw (IO.userError "Expected email contact")

    let mvpBudget := final.departments[0]!.projects[0]!.budget
    mvpBudget ≡ 400000

    let carol := final.departments[0]!.projects[0]!.employees[2]!
    carol.salary ≡ 114000
    carol.contact ≡ Contact.phone "555-0001"

/-! ## Mind-Bending Tests (Recursive Trees) -/

-- Provide BEq and Repr instances for Id
instance [BEq α] : BEq (Id α) := inferInstanceAs (BEq α)
instance [Repr α] : Repr (Id α) := inferInstanceAs (Repr α)

-- Binary tree with values at leaves
inductive Tree (α : Type _) where
  | leaf : α → Tree α
  | node : Tree α → Tree α → Tree α
  deriving BEq, Repr

-- Rose tree (n-ary tree) with values at nodes
inductive Rose (α : Type _) where
  | node : α → List (Rose α) → Rose α
  deriving BEq, Repr

instance [Inhabited α] : Inhabited (Rose α) where
  default := Rose.node default []

-- Plated instances
instance : Plated (Tree α) where
  plate := traversal fun {F} [Applicative F] (f : Tree α → F (Tree α)) (t : Tree α) =>
    match t with
    | Tree.leaf a => pure (Tree.leaf a)
    | Tree.node l r => pure Tree.node <*> f l <*> f r

instance : Plated (Rose α) where
  plate := traversal fun {F} [Applicative F] (f : Rose α → F (Rose α)) (t : Rose α) =>
    match t with
    | Rose.node value children =>
        let rec walkList : List (Rose α) → F (List (Rose α))
          | [] => pure []
          | x :: xs => pure List.cons <*> f x <*> walkList xs
        pure (Rose.node value) <*> walkList children

-- Leaf traversals
private def Tree.walkLeaves {F : Type _ → Type _} [Applicative F]
    (f : α → F α) : Tree α → F (Tree α)
  | Tree.leaf a => pure Tree.leaf <*> f a
  | Tree.node l r => pure Tree.node <*> Tree.walkLeaves f l <*> Tree.walkLeaves f r

private def Tree.leaves : Traversal' (Tree α) α :=
  traversal Tree.walkLeaves

mutual
  private def Rose.walk {α : Type _} {F : Type _ → Type _} [Applicative F]
      (f : α → F α) : Rose α → F (Rose α)
    | Rose.node value children =>
        pure Rose.node <*> f value <*> Rose.walkList f children

  private def Rose.walkList {α : Type _} {F : Type _ → Type _} [Applicative F]
      (f : α → F α) : List (Rose α) → F (List (Rose α))
    | [] => pure []
    | x :: xs => pure List.cons <*> Rose.walk f x <*> Rose.walkList f xs
end

private def Rose.values : Traversal' (Rose α) α :=
  traversal Rose.walk

-- Depth-aware traversals
private def Tree.walkWithDepth {F : Type _ → Type _} [Applicative F]
    (f : Nat → α → F α) (depth : Nat) : Tree α → F (Tree α)
  | Tree.leaf a => pure Tree.leaf <*> f depth a
  | Tree.node l r =>
      pure Tree.node <*> Tree.walkWithDepth f (depth + 1) l <*> Tree.walkWithDepth f (depth + 1) r

private def Rose.walkWithDepth {F : Type _ → Type _} [Applicative F]
    (f : Nat → α → F α) (depth : Nat) : Rose α → F (Rose α)
  | Rose.node value children =>
      let rec walkList (d : Nat) : List (Rose α) → F (List (Rose α))
        | [] => pure []
        | x :: xs => pure List.cons <*> Rose.walkWithDepth f d x <*> walkList d xs
      pure Rose.node <*> f depth value <*> walkList (depth + 1) children

test "Tree: Recursive traversal modifies all leaves" := do
    let tree := Tree.node
      (Tree.leaf 5)
      (Tree.node (Tree.leaf 10) (Tree.leaf 15))

    let doubled := tree & Tree.leaves %~ (· * 2)
    let expected := Tree.node
      (Tree.leaf 10)
      (Tree.node (Tree.leaf 20) (Tree.leaf 30))

    doubled ≡ expected

    let leaves := Fold.toListTraversal Tree.leaves tree
    leaves ≡ [5, 10, 15]

test "Tree: Depth-aware transformation" := do
    let tree := Tree.node
      (Tree.leaf 1)
      (Tree.node (Tree.leaf 2) (Tree.leaf 3))

    let addDepth (depth : Nat) (x : Int) : Id Int :=
      x + (100 * (depth : Int))

    let result := Tree.walkWithDepth addDepth 0 tree
    let expected := Tree.node
      (Tree.leaf 101)
      (Tree.node (Tree.leaf 202) (Tree.leaf 203))

    shouldBe result expected

    let collectWithDepth (depth : Nat) (x : Int) : StateT (List (Nat × Int)) Id Int := do
      modify ((depth, x) :: ·)
      pure x

    let (_, depthInfo) := (Tree.walkWithDepth collectWithDepth 0 tree).run []
    depthInfo.reverse ≡ [(1, 1), (2, 2), (2, 3)]

test "Rose: N-ary recursive traversal" := do
    let tree := Rose.node "root" [
      Rose.node "a" [
        Rose.node "d" [],
        Rose.node "e" []
      ],
      Rose.node "b" [],
      Rose.node "c" [
        Rose.node "f" []
      ]
    ]

    let upper := tree & Rose.values %~ String.toUpper

    match upper with
    | Rose.node value children =>
      value ≡ "ROOT"
      children.length ≡ 3

      match children.head? with
      | some (Rose.node value children) =>
        value ≡ "A"
        children.length ≡ 2
      | none => shouldSatisfy false "Expected first child"

    let nodeCount := cosmosCount tree
    nodeCount ≡ 7

    let values := Fold.toListTraversal Rose.values tree
    values.length ≡ 7

test "Rose: Deeply nested multi-way structure" := do
    let deepTree := Rose.node 1 [
      Rose.node 2 [
        Rose.node 3 [],
        Rose.node 4 [
          Rose.node 5 []
        ]
      ],
      Rose.node 6 [
        Rose.node 7 [
          Rose.node 8 [],
          Rose.node 9 []
        ]
      ]
    ]

    let multiplied := deepTree & Rose.values %~ (· * 10)

    let values := Fold.toListTraversal Rose.values multiplied
    values ≡ [10, 20, 30, 40, 50, 60, 70, 80, 90]

    let treeDepth := depth deepTree
    treeDepth ≡ 4

test "Tree: Recursive validation short-circuits on invalid node" := do
    let tree1 := Tree.node
      (Tree.leaf 5)
      (Tree.node (Tree.leaf 10) (Tree.leaf 15))

    let validatePositive (x : Int) : Option Int :=
      if x > 0 then some x else none

    let result1 := Traversal.traverse' Tree.leaves validatePositive tree1
    result1 ≡? tree1

    let tree2 := Tree.node
      (Tree.leaf 5)
      (Tree.node (Tree.leaf (-10)) (Tree.leaf 15))

    let result2 := Traversal.traverse' Tree.leaves validatePositive tree2
    shouldBeNone result2

    let allPositive := allOf (fun (t : Tree Int) =>
      match t with
      | Tree.leaf x => x > 0
      | Tree.node _ _ => true) tree1
    shouldSatisfy allPositive "allOf reports all leaves positive"

    let allPositive2 := allOf (fun (t : Tree Int) =>
      match t with
      | Tree.leaf x => x > 0
      | Tree.node _ _ => true) tree2
    shouldSatisfy (!allPositive2) "allOf detects negative leaf"

test "Rose: Compute running sum while transforming" := do
    let tree := Rose.node 10 [
      Rose.node 20 [],
      Rose.node 30 [
        Rose.node 40 [],
        Rose.node 50 []
      ]
    ]

    let tr : Traversal' (Rose Int) Int := traversal Rose.walk

    let replaceWithSum (x : Int) : StateT Int Id Int := do
      let sum ← get
      set (sum + x)
      pure sum

    let (transformed, finalSum) := (Traversal.traverse' tr replaceWithSum tree).run 0

    finalSum ≡ 150

    match transformed with
    | Rose.node value _ =>
      value ≡ 0

    let transformedValues := Fold.toListTraversal tr transformed
    transformedValues ≡ [0, 10, 30, 60, 100]

test "Tree: Composed traversal - Tree of Options" := do
    let treeOfOptions : Tree (Option Int) := Tree.node
      (Tree.leaf (some 5))
      (Tree.node (Tree.leaf none) (Tree.leaf (some 15)))

    let composed : Traversal' (Tree (Option Int)) Int :=
      Tree.leaves ∘ somePrism' Int

    let doubled := treeOfOptions & composed %~ (· * 2)
    let expected := Tree.node
      (Tree.leaf (some 10))
      (Tree.node (Tree.leaf none) (Tree.leaf (some 30)))

    doubled ≡ expected

    let collected := Fold.toListTraversal composed treeOfOptions
    collected ≡ [5, 15]

test "Mind: Tree modifies itself - later nodes affected by earlier ones" := do
    let tree := Rose.node 5 [
      Rose.node 10 [],
      Rose.node 15 [
        Rose.node 8 [],
        Rose.node 3 []
      ],
      Rose.node 20 [
        Rose.node 2 []
      ]
    ]

    let tr : Traversal' (Rose Int) Int := traversal Rose.walk

    let modifyBasedOnPrevious (x : Int) : StateT Bool Id Int := do
      let shouldNegate ← get
      if x > 12 then
        set true
        pure x
      else if shouldNegate then
        pure (-x)
      else
        pure x

    let (result, _) := (Traversal.traverse' tr modifyBasedOnPrevious tree).run false

    match result with
    | Rose.node root children =>
      root ≡ 5

      match children with
      | [Rose.node v1 c1, Rose.node v2 c2, Rose.node v3 c3] =>
        v1 ≡ 10
        shouldSatisfy c1.isEmpty "Child 1 has no children"

        v2 ≡ 15
        match c2 with
        | [Rose.node v2_1 _, Rose.node v2_2 _] =>
          v2_1 ≡ (-8)
          v2_2 ≡ (-3)
        | _ => shouldSatisfy false "Expected 2 grandchildren under child 2"

        v3 ≡ 20
        match c3 with
        | [Rose.node v3_1 _] =>
          v3_1 ≡ (-2)
        | _ => shouldSatisfy false "Expected 1 grandchild under child 3"

      | _ => shouldSatisfy false "Expected 3 children"

test "Mind: Deep tree - track and transform based on recursion depth" := do
    let deepTree : Tree Int := Tree.node
      (Tree.node
        (Tree.leaf 1)
        (Tree.leaf 2))
      (Tree.node
        (Tree.node
          (Tree.leaf 3)
          (Tree.leaf 4))
        (Tree.leaf 5))

    let transformWithDepth (depth : Nat) (x : Int) : Id Int :=
      x * ((depth + 1) : Int)

    let result := Tree.walkWithDepth transformWithDepth 0 deepTree

    let collectValues (depth : Nat) (x : Int) : StateT (List (Nat × Int)) Id Int := do
      modify ((depth, x) :: ·)
      pure x

    let (_, depthValuePairs) := (Tree.walkWithDepth collectValues 0 deepTree).run []

    depthValuePairs.reverse ≡ [(2, 1), (2, 2), (3, 3), (3, 4), (2, 5)]

    let collectTransformed (_depth : Nat) (x : Int) : StateT (List Int) Id Int := do
      modify (x :: ·)
      pure x

    let (_, transformedValues) := (Tree.walkWithDepth collectTransformed 0 result).run []

    transformedValues.reverse ≡ [3, 6, 12, 16, 15]

test "Plated: Bottom-up tree simplification" := do
    let tree : Tree Int := Tree.node
      (Tree.node (Tree.leaf 5) (Tree.leaf 5))
      (Tree.node
        (Tree.leaf 3)
        (Tree.node (Tree.leaf 7) (Tree.leaf 7)))

    let simplify (t : Tree Int) : Tree Int :=
      match t with
      | Tree.node (Tree.leaf x) (Tree.leaf y) =>
          if x == y then Tree.leaf (x * 2) else t
      | _ => t

    let simplified := transform simplify tree

    let expected := Tree.node
      (Tree.leaf 10)
      (Tree.node (Tree.leaf 3) (Tree.leaf 14))

    simplified ≡ expected

test "Plated: Iterative expression simplification" := do
    let nested : Rose Int := Rose.node 1 [
      Rose.node 2 [
        Rose.node 3 [
          Rose.node 4 []
        ]
      ]
    ]

    let flattenSingle (t : Rose Int) : Option (Rose Int) :=
      match t with
      | Rose.node x [Rose.node y cs] => some (Rose.node (x + y) cs)
      | _ => none

    let flattened := rewrite flattenSingle nested

    let expected := Rose.node 10 []

    flattened ≡ expected

test "Plated: universeList, findOf, anyOf utilities" := do
    let tree : Rose String := Rose.node "root" [
      Rose.node "child1" [
        Rose.node "grandchild1" [],
        Rose.node "target" []
      ],
      Rose.node "child2" []
    ]

    let allNodes := universeList tree
    allNodes.length ≡ 5

    let found := findOf (fun (t : Rose String) =>
      match t with
      | Rose.node "target" _ => true
      | _ => false) tree

    match found with
    | some (Rose.node v _) => v ≡ "target"
    | none => shouldSatisfy false "Expected to find target"

    let hasTarget := anyOf (fun (t : Rose String) =>
      match t with
      | Rose.node "target" _ => true
      | _ => false) tree
    shouldSatisfy hasTarget "anyOf finds target"

    let hasMissing := anyOf (fun (t : Rose String) =>
      match t with
      | Rose.node "missing" _ => true
      | _ => false) tree
    shouldSatisfy (!hasMissing) "anyOf correctly reports missing"

/-! ## Stress Tests -/

test "Stress: Large list (1000 elements) traversal" := do
  let largeList : List Int := (List.range 1000).map (Int.ofNat ·)
  let tr : Traversal' (List Int) Int := Traversal.eachList

  let result := largeList & tr %~ (· + 1)

  result.length ≡ 1000
  result.head? ≡? 1
  result.getLast? ≡? 1000

test "Stress: Large list fold to list" := do
  let largeList : List Int := (List.range 500).map (Int.ofNat ·)
  let tr : Traversal' (List Int) Int := Traversal.eachList

  let result := largeList ^.. tr

  result.length ≡ 500
  result ≡ largeList

test "Stress: Nested list traversal" := do
  let nestedList : List (List Int) := [[1, 2], [3, 4, 5], [6]]

  let outerTr : Traversal' (List (List Int)) (List Int) := Traversal.eachList
  let innerTr : Traversal' (List Int) Int := Traversal.eachList

  let composed : Traversal' (List (List Int)) Int := outerTr ∘ innerTr
  let result := nestedList & composed %~ (· * 10)

  result ≡ ([[10, 20], [30, 40, 50], [60]])

test "Stress: Deep lens composition (5 levels)" := do
  let nested : ((((Int × Int) × Int) × Int) × Int) := ((((1, 2), 3), 4), 5)

  let l1 : Lens' ((((Int × Int) × Int) × Int) × Int) (((Int × Int) × Int) × Int) := _1
  let l2 : Lens' (((Int × Int) × Int) × Int) ((Int × Int) × Int) := _1
  let l3 : Lens' ((Int × Int) × Int) (Int × Int) := _1
  let l4 : Lens' (Int × Int) Int := _1

  let composed : Lens' (((((Int × Int) × Int) × Int) × Int)) Int := l1 ∘ l2 ∘ l3 ∘ l4

  nested ^. composed ≡ 1
  (nested & composed .~ 99) ^. composed ≡ 99

end CollimatorTests.CompositionTests
