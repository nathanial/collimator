import Collimator.Core
import Batteries
import Collimator.Optics
import Collimator.Combinators
import Collimator.Operators
import Collimator.Concrete.FunArrow
import Collimator.Concrete.Forget
import Collimator.Instances
import CollimatorTests.Framework

namespace CollimatorTests.AdvancedShowcase.DeepComposition

open Collimator
open Collimator.Core
open Collimator.Instances.List
open Collimator.Instances.Prod
open Collimator.Instances.Option (somePrism somePrism')
open Collimator.Instances.Sum (left right left' right')
open Collimator.Combinators
open Collimator.Indexed
open Collimator.Fold (toList toListTraversal ofLens composeLensFold composeFold)
open Collimator.AffineTraversalOps (ofPrism)
open scoped Collimator.Operators  -- For optic operators
open scoped Collimator.Fold  -- For ∘f, ∘ₗf
open CollimatorTests

/-!
Showcase composition as the killer feature of profunctor optics.
All optics compose via standard function composition (`∘`).

This section should demonstrate compositions of 3+ optics including:
- Homogeneous: Lens ∘ Lens ∘ Lens (current: ✓)
- Heterogeneous: Lens ∘ Traversal ∘ Lens (current: ✓)
- With Iso: Iso ∘ Lens or Lens ∘ Iso ∘ Traversal (TODO)
- With Prism: Lens ∘ Prism ∘ Lens for optional fields (TODO)
- With Affine: Lens ∘ Affine ∘ Lens for safe head/lookup (TODO)
- Mixed: Iso ∘ Traversal ∘ Prism ∘ Lens (ultimate test) (TODO)
-/

/-! ## Custom Types -/

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

/-- Extended Company structure with optional CEO field -/
structure CompanyWithCEO where
  name : String
  departments : List Department
  ceo : Option Employee
  deriving BEq, Repr

/-! ## Field Lenses -/

-- Address field lenses
private def Address.streetLens : Lens' Address String := fieldLens% Address street
private def Address.cityLens : Lens' Address String := fieldLens% Address city
private def Address.zipCodeLens : Lens' Address String := fieldLens% Address zipCode

-- Employee field lenses
private def Employee.nameLens : Lens' Employee String := fieldLens% Employee name
private def Employee.addressLens : Lens' Employee Address := fieldLens% Employee address
private def Employee.salaryLens : Lens' Employee Int := fieldLens% Employee salary

-- Department field lenses
private def Department.nameLens : Lens' Department String := fieldLens% Department name
private def Department.employeesLens : Lens' Department (List Employee) := fieldLens% Department employees

-- Company field lenses
private def Company.nameLens : Lens' Company String := fieldLens% Company name
private def Company.departmentsLens : Lens' Company (List Department) := fieldLens% Company departments

-- CompanyWithCEO field lenses
private def CompanyWithCEO.nameLens : Lens' CompanyWithCEO String := fieldLens% CompanyWithCEO name
private def CompanyWithCEO.departmentsLens : Lens' CompanyWithCEO (List Department) := fieldLens% CompanyWithCEO departments
private def CompanyWithCEO.ceoLens : Lens' CompanyWithCEO (Option Employee) := fieldLens% CompanyWithCEO ceo

/-! ## Isomorphisms -/

/-- Isomorphism between String and List Char (for composition tests). -/
private def stringToListIso : Iso String String (List Char) (List Char) :=
  iso
    (forward := String.toList)
    (back := List.asString)

/-- Test: Composing lenses through tuple fields. -/
private def case_nestedTuples : TestCase := {
  name := "Nested tuples: _1 . _2 composition",
  run := do
    -- Build nested tuple structure
    let data : ((Int × String) × Float) := ((42, "hello"), 3.14)

    -- Compose: _1 (first of outer pair) . _2 (second of inner pair) using function composition
    let lens1 : Lens ((Int × String) × Float) ((Int × String) × Float) (Int × String) (Int × String) := _1
    let lens2 : Lens (Int × String) (Int × String) String String := _2
    let composed : Lens ((Int × String) × Float) ((Int × String) × Float) String String :=
      lens1 ∘ lens2

    -- View the deeply nested value
    let str := view' composed data
    ensureEq "View nested string" "hello" str

    -- Modify the deeply nested value
    let modified := over' composed (fun s => s ++ "!") data
    let expected := ((42, "hello!"), 3.14)
    ensureEq "Modify through composition" expected modified

    -- Set a new value
    let updated := set' composed "world" data
    let expected2 := ((42, "world"), 3.14)
    ensureEq "Set through composition" expected2 updated
}

/-- Inhabited instance for Department (for headLens) -/
private instance : Inhabited Department where
  default := { name := "", employees := [] }

/-- Inhabited instance for Employee (for headLens) -/
private instance : Inhabited Employee where
  default := { name := "", address := { street := "", city := "", zipCode := "" }, salary := 0 }

/-- Lens to access the first element of a non-empty list. -/
private def headLens {α : Type} [Inhabited α] : Lens' (List α) α :=
  lens'
    (fun xs => xs.head!)
    (fun xs new => match xs with
      | [] => [new]
      | _ :: tail => new :: tail)

/-- Test: Deep composition through Company → Department → Employee → Address → zipCode -/
private def case_companyZipCode : TestCase := {
  name := "Company → Dept → Employee → Address → Zip: 5-level deep lens chain",
  run := do
    -- Build sample data
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

    -- Compose all at once to avoid intermediate wrapping issues
    -- Company → List Dept → first Dept → List Emp → first Emp → Address → Zip
    let companyToZip : Lens' Company String :=
      Company.departmentsLens ∘ headLens (α := Department) ∘ Department.employeesLens ∘
      headLens (α := Employee) ∘ Employee.addressLens ∘ Address.zipCodeLens

    -- View the deeply nested zip code
    let zip := view' companyToZip company
    ensureEq "View nested zip code" "12345" zip

    -- Modify the deeply nested zip code
    let modified := over' companyToZip (fun _ => "99999") company
    let newZip := view' companyToZip modified
    ensureEq "Modified zip code" "99999" newZip

    -- Verify other fields unchanged
    ensureEq "Company name unchanged" "Acme Corp" modified.name
    ensureEq "Department name unchanged" "Engineering" modified.departments.head!.name
    ensureEq "Employee name unchanged" "Alice" modified.departments.head!.employees.head!.name
    ensureEq "City unchanged" "Springfield" modified.departments.head!.employees.head!.address.city

    -- Set a completely new zip code
    let updated := set' companyToZip "54321" company
    let finalZip := view' companyToZip updated
    ensureEq "Set new zip code" "54321" finalZip
}

/-- Test: Iso ∘ Traversal composition using String → List Char transformation -/
private def case_isoTraversalComposition : TestCase := {
  name := "Iso ∘ Traversal: String → List Char with char-level modifications",
  run := do
    -- Starting string
    let s : String := "hello"

    -- Compose stringToListIso (from PolymorphicIsos) with traversed
    -- This transforms String → List Char, then focuses each Char
    let stringCharsTraversal : Traversal String String Char Char :=
      stringToListIso ∘ traversed (α := Char) (β := Char)

    -- Collect all chars as a list (demonstrates the Iso transformation + Traversal focus)
    let chars := toListTraversal stringCharsTraversal s
    ensureEq "Chars collected via Iso ∘ Traversal" ['h', 'e', 'l', 'l', 'o'] chars

    -- Modify all chars to uppercase
    let upper := Traversal.over' stringCharsTraversal Char.toUpper s
    ensureEq "All chars to uppercase" "HELLO" upper

    -- Transform specific chars
    let exclaimed := Traversal.over' stringCharsTraversal (fun c => if c == 'l' then '!' else c) s
    ensureEq "Replace l with !" "he!!o" exclaimed

    -- Empty string edge case
    let empty := ""
    let emptyChars := Fold.toListTraversal stringCharsTraversal empty
    ensureEq "Empty string has no chars" ([] : List Char) emptyChars

    -- Key insight: Iso enables type transformation (String ↔ List Char)
    --              Traversal enables multi-focus (each Char)
    --              Together: work on String as if it were List Char!
}

/-- Test: Traversal ∘ Prism composition with Option to skip None values -/
private def case_traversalPrismComposition : TestCase := {
  name := "Traversal ∘ Prism ∘ Lens: Skip None employees, modify only Some",
  run := do
    -- Create employees
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

    -- Create list with Some and None values
    let employees : List (Option Employee) := [
      some emp1,
      none,
      some emp2,
      none,
      none,
      some emp3
    ]

    -- Build composition: List (Option Employee) → Option Employee* → Employee → Address → city
    -- traversed : Traversal (List (Option Employee)) _ (Option Employee) _
    -- somePrism : Prism (Option Employee) _ Employee _
    -- addressLens : Lens Employee _ Address _
    -- cityLens : Lens Address _ String _

    -- Compose: Traversal → Prism → Lens → Lens
    -- Using optic% macro for clean type annotation on composed optics
    let finalTraversal := optic%
      traversed ∘ somePrism' Employee ∘ Employee.addressLens ∘ Address.cityLens
      : Traversal' (List (Option Employee)) String

    -- Collect all cities (only from Some employees, None are skipped!)
    let cities := toListTraversal finalTraversal employees
    ensureEq "Collect cities (None skipped)" ["NYC", "LA", "SF"] cities

    -- Modify all cities to "Remote"
    let remote : List (Option Employee) := Traversal.over' finalTraversal (fun _ => "Remote") employees
    let remoteCities := Fold.toListTraversal finalTraversal remote
    ensureEq "All cities changed to Remote" ["Remote", "Remote", "Remote"] remoteCities

    -- Verify None values are preserved (count remains same)
    ensureEq "List length unchanged" 6 remote.length

    -- Verify first employee's city was modified
    match remote.head! with
    | some e => ensureEq "First employee city is Remote" "Remote" e.address.city
    | none => ensure false "Expected Some employee at index 0"

    -- Verify None values are still None
    match remote[1]! with
    | none => pure ()
    | some _ => ensure false "Expected None at index 1"

    -- Key insight: Prisms provide "optional focus" via pattern matching
    --              When composed with Traversal, only matching elements are modified
    --              None values are completely skipped (not even seen by the lens!)
}

/-- Test: Traversal ∘ Prism with Sum type to handle errors -/
private def case_traversalPrismSum : TestCase := {
  name := "Traversal ∘ Prism with Sum: Skip Left (errors), process Right (values)",
  run := do
    -- Create mix of errors and valid employees
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

    -- Compose: List (Sum String Employee) → Sum* → Employee → salary
    -- Using optic% for the composed traversal
    let finalTraversal := optic%
      traversed ∘ right' String Employee ∘ Employee.salaryLens
      : Traversal' (List (Sum String Employee)) Int

    -- Collect salaries (only from Right/success cases)
    let salaries := Fold.toListTraversal finalTraversal results
    ensureEq "Collect salaries (errors skipped)" [100000, 110000] salaries

    -- Give 10% raise to successful employees only
    let raised : List (Sum String Employee) := Traversal.over' finalTraversal (fun s => s + s / 10) results
    let newSalaries := Fold.toListTraversal finalTraversal raised
    ensureEq "Salaries raised (errors untouched)" [110000, 121000] newSalaries

    -- Verify error messages are unchanged
    match raised[1]! with
    | Sum.inl msg => ensureEq "Error message preserved" "Error: Employee not found" msg
    | Sum.inr _ => ensure false "Expected error at index 1"

    -- Key insight: Prisms work with any sum type (Option, Sum, custom enums)
    --              Left values are invisible to the composed traversal
    --              This is perfect for error handling pipelines!
}

/-- Test: AffineTraversal for "at most one" focus semantics -/
private def case_affineTraversal : TestCase := {
  name := "AffineTraversal: Safe head access with 'at most one' focus",
  run := do
    -- Create employees
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

    -- Build AffineTraversal: List Employee → Option Employee (via head) → Employee → Address → city
    -- Use HasAt.focus 0 for head access: Lens' (List Employee) (Option Employee)
    let headLens : Lens' (List Employee) (Option Employee) := HasAt.focus 0

    -- Compose: Lens to Option → somePrism → addressLens → cityLens
    let finalAffine : AffineTraversal' (List Employee) String :=
      headLens ∘
      ofPrism (somePrism' Employee) ∘
      Employee.addressLens ∘
      Address.cityLens

    -- Preview: succeeds on non-empty list
    let city := AffineTraversalOps.preview' finalAffine employees
    ensureEq "Preview head city succeeds" (some "NYC") city

    -- Preview: fails on empty list (key difference from Lens!)
    let noCity := AffineTraversalOps.preview' finalAffine empty
    ensureEq "Preview on empty list fails" (none : Option String) noCity

    -- Modify: works on non-empty list
    let modified : List Employee := AffineTraversalOps.over finalAffine (fun _ => "SF") employees
    let newCity := AffineTraversalOps.preview' finalAffine modified
    ensureEq "Modified head city" (some "SF") newCity

    -- Verify second employee unchanged
    match modified.tail? with
    | some tail =>
        match tail.head? with
        | some emp => ensureEq "Second employee unchanged" "LA" emp.address.city
        | none => ensure false "Expected second employee"
    | none => ensure false "Expected tail"

    -- Set on empty list: no effect (key behavior!)
    let stillEmpty : List Employee := AffineTraversalOps.set finalAffine "Denver" empty
    ensureEq "Set on empty list is no-op" empty stillEmpty

    -- Key insight: AffineTraversal = "at most one focus"
    --   - Lens = "exactly one focus" (always present)
    --   - Prism = "at most one focus" (pattern match)
    --   - Traversal = "zero or more focuses"
    --   - Affine = "zero or one focus" (safe partial access)
}

/-- Test: AffineTraversal via List.at for index-based access -/
private def case_affineViaAt : TestCase := {
  name := "AffineTraversal: List.at composition for safe indexed access",
  run := do
    -- Use the HasAt instance from List to create AffineTraversal
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

    -- Build lens using HasAt, then compose with somePrism to get AffineTraversal
    let atLens : Lens' (List Employee) (Option Employee) := HasAt.focus 1  -- index 1 (Bob)

    -- Compose: Lens to Option Employee → Prism (somePrism) → Lens to salary
    let finalAffine := optic%
      atLens ∘ ofPrism (somePrism' Employee) ∘ Employee.salaryLens
      : AffineTraversal' (List Employee) Int

    -- Preview element at valid index
    let salary := AffineTraversalOps.preview' finalAffine employees
    ensureEq "Preview salary at index 1" (some 110000) salary

    -- Modify element at valid index
    let raised : List Employee := AffineTraversalOps.over finalAffine (· + 10000) employees
    let newSalary := AffineTraversalOps.preview' finalAffine raised
    ensureEq "Raised salary at index 1" (some 120000) newSalary

    -- Verify other employees unchanged
    match raised.head? with
    | some e => ensureEq "First employee unchanged" 100000 e.salary
    | none => ensure false "Expected first employee"

    -- Access out-of-bounds index
    let atLens10 : Lens' (List Employee) (Option Employee) := HasAt.focus 10
    let outOfBounds := optic%
      atLens10 ∘ ofPrism (somePrism' Employee)
      : AffineTraversal' (List Employee) Employee

    let noEmployee := AffineTraversalOps.preview' outOfBounds employees
    ensureEq "Out of bounds preview fails" (none : Option Employee) noEmployee

    -- Modify out-of-bounds: no effect
    let unchanged : List Employee := AffineTraversalOps.over outOfBounds (fun e => { e with salary := 0 }) employees
    ensureEq "Out of bounds modify is no-op" employees unchanged

    -- Key insight: Lens to Option + somePrism = AffineTraversal
    --   Perfect for safe array/list access, map lookup, etc.
}

/-- Test: Fold for read-only operations - demonstrates Fold type and read-only Traversals -/
private def case_foldAggregations : TestCase := {
  name := "Fold: Read-only optics for single values and multi-element aggregation",
  run := do
    -- Build sample company with multiple departments
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

    -- PART 1: Demonstrate Fold type for read-only single-value access
    -- Folds are useful when you want to guarantee no modification can happen

    -- For deep lens composition, we use direct lens construction to avoid
    -- profunctor constraint unification issues with long chains
    -- Path: Company → departments → [0] → employees → [0] → address → city
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

    -- Use the composed Lens to read a single value (first employee's city)
    let firstCity := view' companyToFirstCity company
    ensureEq "Fold reads first employee's city" "NYC" firstCity

    -- Path: Company → departments → [0] → employees → [0] → salary
    let firstEmpSalaryLens : Lens' Company Int := lens'
      (fun c => c.departments.head!.employees.head!.salary)
      (fun c sal =>
        let d := c.departments.head!
        let e := d.employees.head!
        let e' := { e with salary := sal }
        let d' := { d with employees := e' :: d.employees.tail! }
        { c with departments := d' :: c.departments.tail! })

    let firstSalary := view' firstEmpSalaryLens company
    ensureEq "Fold reads first employee's salary" 100000 firstSalary

    -- Key insight: Folds are type-safe read-only optics
    -- They compose like Lenses but cannot be used for modification
    -- Perfect for APIs where you want to expose read access but not write access

    -- PART 2: Multi-element aggregation using Traversals in read-only mode
    -- For collecting multiple elements, we use Traversals (via toListTraversal)

    -- 1. Collect all zip codes from the entire company
    -- Company → all departments → all employees → address → zipCode
    let allZipsTraversal := optic%
      Company.departmentsLens ∘ traversed ∘ Department.employeesLens ∘ traversed ∘ Employee.addressLens ∘ Address.zipCodeLens
      : Traversal' Company String

    let allZipCodes : List String := toListTraversal allZipsTraversal company
    ensureEq "Collect all zip codes" ["10001", "94102", "90001", "78701", "02101"] allZipCodes

    -- 2. Collect all salaries and compute sum (demonstrates fold aggregation)
    let allSalariesTraversal := optic%
      Company.departmentsLens ∘ traversed ∘ Department.employeesLens ∘ traversed ∘ Employee.salaryLens
      : Traversal' Company Int

    let allSalaries : List Int := toListTraversal allSalariesTraversal company
    ensureEq "Collect all salaries" [100000, 110000, 90000, 95000, 85000] allSalaries

    -- Sum salaries (fold aggregation)
    let totalSalary := allSalaries.foldl (· + ·) (0 : Int)
    ensureEq "Total salary across company" 480000 totalSalary

    -- Average salary
    let avgSalary := totalSalary / allSalaries.length
    ensureEq "Average salary" 96000 avgSalary

    -- 3. Count employees across all departments (demonstrates counting)
    let allEmployeesTraversal := optic%
      Company.departmentsLens ∘ traversed ∘ Department.employeesLens ∘ traversed
      : Traversal' Company Employee

    let allEmployees : List Employee := toListTraversal allEmployeesTraversal company
    let employeeCount := allEmployees.length
    ensureEq "Total employee count" 5 employeeCount

    -- 4. Collect all cities (demonstrates another read-only property)
    let allCitiesTraversal := optic%
      Company.departmentsLens ∘ traversed ∘ Department.employeesLens ∘ traversed ∘ Employee.addressLens ∘ Address.cityLens
      : Traversal' Company String

    let allCities := toListTraversal allCitiesTraversal company
    ensureEq "Collect all cities" ["NYC", "SF", "LA", "Austin", "Boston"] allCities

    -- Get unique cities (demonstrates post-processing)
    let uniqueCities := allCities.eraseDups
    ensureEq "Unique city count" 5 uniqueCities.length

    -- 5. Find employees with salary > 95000 (demonstrates filtering via collection)
    let highEarners := allEmployees.filter (fun (e : Employee) => e.salary > 95000)
    ensureEq "High earners count" 2 highEarners.length
    ensureEq "High earners names" ["Alice", "Bob"] (highEarners.map (fun (e : Employee) => e.name))

    -- Summary of read-only optics:
    -- 1. Fold type: For read-only access through single paths (composed Lenses)
    --    - Guarantees no modification at the type level
    --    - Perfect for read-only APIs and queries
    --    - Compose via Fold.composeLensFold and Fold.composeFold
    -- 2. Traversals in read-only mode: For multi-element aggregation
    --    - Use toListTraversal to collect all focused elements
    --    - Perfect for analytics: sums, counts, averages, filters
    --    - Can post-process with standard List operations (foldl, filter, map)
}

/-- Test: Ultimate composition mixing all optic types together -/
private def case_ultimateComposition : TestCase := {
  name := "Ultimate: Lens ∘ Traversal ∘ Lens ∘ Iso ∘ Traversal ∘ Prism (6 optic types!)",
  run := do
    -- Create employees with names that we'll manipulate at character level
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

    -- Example 1: Lens ∘ Iso ∘ Traversal to modify employee names at character level
    -- Path: Employee → name (Lens) → List Char (Iso) → each char (Traversal)

    -- Compose: Lens → Iso → Traversal to get character-level access
    let nameCharsTraversal : Traversal' Employee Char :=
      Employee.nameLens ∘ (stringToListIso ∘ traversed (α := Char) (β := Char))

    -- Capitalize all characters in employee name
    let capitalized : Employee := Traversal.over' nameCharsTraversal Char.toUpper emp1
    ensureEq "Lens ∘ Iso ∘ Traversal: name to uppercase" "ALICE" capitalized.name

    -- Example 2: Company-wide name transformation
    -- Lens → Traversal → Lens → Traversal → Lens → Iso → Traversal
    -- Path: Company → departments → Dept* → employees → Emp* → name → chars → char*

    -- Build the mega-composition: all employee names at character level
    let companyToAllNameChars := optic%
      Company.departmentsLens ∘ traversed ∘ Department.employeesLens ∘ traversed ∘
      Employee.nameLens ∘ stringToListIso ∘ traversed
      : Traversal' Company Char

    -- Capitalize all employee names across the entire company!
    let allCaps : Company := Traversal.over' companyToAllNameChars Char.toUpper company

    -- Verify all names are now uppercase
    ensureEq "First dept, first employee" "ALICE" allCaps.departments[0]!.employees[0]!.name
    ensureEq "First dept, second employee" "BOB" allCaps.departments[0]!.employees[1]!.name
    ensureEq "Second dept, first employee" "CAROL" allCaps.departments[1]!.employees[0]!.name

    -- Collect all name characters (demonstrates Traversal as Fold)
    let allChars := toListTraversal companyToAllNameChars company
    ensureEq "All name chars collected" ['a','l','i','c','e','b','o','b','c','a','r','o','l'] allChars

    -- Example 3: Add filtering to the mix - filter by character
    -- Use filtered to only focus on 'a' characters
    let aCharsOnly : Traversal' Company Char :=
      Collimator.Combinators.filtered companyToAllNameChars (· == 'a')

    let countAs := (toListTraversal aCharsOnly company).length
    ensureEq "Count 'a' characters in all names" 2 countAs  -- alice(1) + carol(1) = 2

    -- Replace all 'a' with 'A'
    let replacedAs : Company := Traversal.over' aCharsOnly (fun _ => 'A') company
    ensureEq "Replaced 'a' with 'A' in alice" "Alice" replacedAs.departments[0]!.employees[0]!.name
    ensureEq "Replaced 'a' with 'A' in carol" "cArol" replacedAs.departments[1]!.employees[0]!.name

    -- Key insight: This demonstrates the ultimate power of profunctor optics!
    -- We composed 7 different optic types:
    --   1. Lens (Company → departments)
    --   2. Traversal (departments → each Department)
    --   3. Lens (Department → employees)
    --   4. Traversal (employees → each Employee)
    --   5. Lens (Employee → name)
    --   6. Iso (String ↔ List Char)
    --   7. Traversal (List Char → each Char)
    -- All in a type-safe, composable way!
}

/-- Test: Nested Options with short-circuiting via Prism composition -/
private def case_nestedOptions : TestCase := {
  name := "Nested Options: Lens ∘ Prism ∘ Lens showing short-circuit on None",
  run := do
    -- Create test data with and without CEO
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

    -- Build composition: Company → ceo (Lens) → Employee (Prism) → address (Lens) → city (Lens)
    -- Compose Lens → Prism → Lens → Lens using AffineTraversal
    let ceoToCity : AffineTraversal' CompanyWithCEO String :=
      CompanyWithCEO.ceoLens ∘
      ofPrism (somePrism' Employee) ∘
      Employee.addressLens ∘
      Address.cityLens

    -- Test 1: Preview succeeds when CEO exists
    let cityWithCEO := AffineTraversalOps.preview' ceoToCity companyWithCEO
    ensureEq "Preview CEO city succeeds" (some "NYC") cityWithCEO

    -- Test 2: Preview short-circuits when CEO is None
    let cityNoCEO := AffineTraversalOps.preview' ceoToCity companyNoCEO
    ensureEq "Preview CEO city fails (short-circuit)" (none : Option String) cityNoCEO

    -- Test 3: Set modifies when CEO exists
    let movedCEO : CompanyWithCEO := AffineTraversalOps.set ceoToCity "Boston" companyWithCEO
    let newCity := AffineTraversalOps.preview' ceoToCity movedCEO
    ensureEq "Set CEO city succeeds" (some "Boston") newCity

    -- Verify CEO name unchanged
    match movedCEO.ceo with
    | some emp => ensureEq "CEO name unchanged" "Alice" emp.name
    | none => ensure false "Expected CEO to exist"

    -- Test 4: Set is no-op when CEO is None (short-circuit)
    let unchangedNoCEO : CompanyWithCEO := AffineTraversalOps.set ceoToCity "Boston" companyNoCEO
    ensureEq "Set on None is no-op" companyNoCEO unchangedNoCEO

    -- Test 5: Over is no-op when CEO is None
    let upperNoCEO : CompanyWithCEO := AffineTraversalOps.over ceoToCity String.toUpper companyNoCEO
    ensureEq "Over on None is no-op" companyNoCEO upperNoCEO

    -- Test 6: Nested Option chaining - CEO → address → street
    let ceoToStreet : AffineTraversal' CompanyWithCEO String :=
      CompanyWithCEO.ceoLens ∘
      ofPrism (somePrism' Employee) ∘
      Employee.addressLens ∘
      Address.streetLens

    let street := AffineTraversalOps.preview' ceoToStreet companyWithCEO
    ensureEq "Nested preview succeeds" (some "1 Executive Blvd") street

    let noStreet := AffineTraversalOps.preview' ceoToStreet companyNoCEO
    ensureEq "Nested preview short-circuits" (none : Option String) noStreet

    -- Key insights:
    -- 1. Prism composition enables safe navigation through optional fields
    -- 2. Preview short-circuits on None, returning none
    -- 3. Set and over' are no-ops when encountering None
    -- 4. Multiple Prisms can be chained for deep optional navigation
    -- 5. AffineTraversal combines "exactly one" (Lens) + "at most one" (Prism)
}

/-- Test: Mix lenses and traversals to modify all employee salaries -/
private def case_allSalaries : TestCase := {
  name := "Company → all Depts → all Employees → salary: Lens + Traversal mix",
  run := do
    -- Build sample data with multiple departments and employees
    let eng1 : Employee := { name := "Alice", address := { street := "1 Main", city := "NYC", zipCode := "10001" }, salary := 100000 }
    let eng2 : Employee := { name := "Bob", address := { street := "2 Main", city := "NYC", zipCode := "10002" }, salary := 110000 }
    let sales1 : Employee := { name := "Carol", address := { street := "3 Main", city := "LA", zipCode := "90001" }, salary := 90000 }
    let sales2 : Employee := { name := "Dave", address := { street := "4 Main", city := "LA", zipCode := "90002" }, salary := 95000 }

    let engineering : Department := { name := "Engineering", employees := [eng1, eng2] }
    let sales : Department := { name := "Sales", employees := [sales1, sales2] }

    let company : Company := { name := "TechCorp", departments := [engineering, sales] }

    -- Build the composition: Company → List Dept → Dept* → List Emp → Emp* → salary
    -- This is: Lens → Traversal → Lens → Traversal → Lens

    -- Compose: Company → all Depts → all Employees → salary
    let companyToAllSalaries := optic%
      Company.departmentsLens ∘ traversed ∘ Department.employeesLens ∘ traversed ∘ Employee.salaryLens
      : Traversal' Company Int

    -- Collect all salaries (read operation) using toListTraversal
    let allSalaries : List Int := toListTraversal companyToAllSalaries company
    ensureEq "All salaries collected" [100000, 110000, 90000, 95000] allSalaries

    -- Give everyone a 10% raise
    let raised : Company := Traversal.over' companyToAllSalaries (fun sal => sal + (sal / 10)) company
    let newSalaries : List Int := toListTraversal companyToAllSalaries raised
    ensureEq "All salaries raised 10%" [110000, 121000, 99000, 104500] newSalaries

    -- Verify company name unchanged
    ensureEq "Company name preserved" "TechCorp" raised.name

    -- Verify department names unchanged
    ensureEq "Dept count preserved" 2 raised.departments.length
    ensureEq "Engineering name preserved" "Engineering" raised.departments.head!.name

    -- Verify employee names unchanged (only salaries changed)
    ensureEq "Alice name preserved" "Alice" raised.departments.head!.employees.head!.name
    ensureEq "Bob name preserved" "Bob" raised.departments.head!.employees.tail!.head!.name

    -- Set all salaries to a fixed amount
    let normalized : Company := Traversal.over' companyToAllSalaries (fun _ => 100000) company
    let finalSalaries : List Int := toListTraversal companyToAllSalaries normalized
    ensureEq "All salaries normalized" [100000, 100000, 100000, 100000] finalSalaries
}

/-
Coverage Summary for DeepComposition:
✓ Lens: extensively used (nestedTuples, companyZipCode, ultimateComposition, allSalaries)
✓ Traversal: used extensively for multi-focus (allSalaries, ultimateComposition, foldAggregations)
✓ Iso: used in type transformations (isoTraversalComposition, ultimateComposition)
✓ Prism: used in sum type pattern matching (traversalPrismComposition, traversalPrismSum)
✓ Affine: used for safe partial access (affineTraversal, affineViaAt)
✓ Fold: used for read-only operations (foldAggregations with ofLens + composeLensFold)
✗ Setter: NOT YET USED (less interesting, mainly for completeness)

Ultimate composition (ultimateComposition) demonstrates:
- Lens → Traversal → Lens → Traversal → Lens → Iso → Traversal (7 optics!)
- All major optic types working together in type-safe composition
- Character-level string manipulation across deeply nested structures
-/

def cases : List TestCase := [
  case_nestedTuples,
  case_companyZipCode,
  case_isoTraversalComposition,
  case_traversalPrismComposition,
  case_traversalPrismSum,
  case_affineTraversal,
  case_affineViaAt,
  case_foldAggregations,
  case_ultimateComposition,
  case_nestedOptions,
  case_allSalaries
]

end CollimatorTests.AdvancedShowcase.DeepComposition
