import Collimator.Optics
import Collimator.Combinators
import Collimator.Operators
import Collimator.Poly
import Collimator.Instances.List
import CollimatorTests.Framework

namespace CollimatorTests.AdvancedShowcase.HeterogeneousCompositions

open Collimator
open Collimator.Poly
open Collimator.Combinators
open Collimator.Operators
open Collimator.Instances
open CollimatorTests

open scoped Collimator.Operators

/-!
# Heterogeneous Compositions

Demonstrate mixing different optic types in deep compositions:
- Lens ∘ Traversal ∘ Prism ∘ Lens chains
- Type inference working across complex compositions
- The resulting optic type follows the subtyping hierarchy
- Practical examples: querying/updating nested data structures
- Comparison with hand-written imperative code
-/

/-! ## Data Structures -/

/-- Contact information that may or may not be present -/
private inductive Contact where
  | email : String → Contact
  | phone : String → Contact
  | none : Contact
  deriving BEq, Repr, Inhabited

/-- Employee with optional contact info -/
private structure Employee where
  name : String
  salary : Nat
  contact : Contact
  deriving BEq, Repr, Inhabited

/-- Project with a list of assigned employees -/
private structure Project where
  title : String
  budget : Nat
  employees : List Employee
  deriving BEq, Repr, Inhabited

/-- Department containing multiple projects -/
private structure Department where
  name : String
  projects : List Project
  deriving BEq, Repr, Inhabited

/-- Company with multiple departments -/
private structure Company where
  name : String
  departments : List Department
  deriving BEq, Repr, Inhabited

/-- Address that can be domestic or international -/
private inductive Address where
  | domestic : String → String → Address  -- street, city
  | international : String → String → String → Address  -- street, city, country
  deriving BEq, Repr, Inhabited

/-- Person with optional address -/
private structure Person where
  name : String
  age : Nat
  address : Option Address
  deriving BEq, Repr, Inhabited

/-- Team containing multiple people -/
private structure Team where
  name : String
  members : List Person
  deriving BEq, Repr, Inhabited

/-! ## Lenses -/

private def salaryLens : Lens' Employee Nat :=
  lens' (fun e => e.salary) (fun e s => { e with salary := s })

private def contactLens : Lens' Employee Contact :=
  lens' (fun e => e.contact) (fun e c => { e with contact := c })

private def employeesLens : Lens' Project (List Employee) :=
  lens' (fun p => p.employees) (fun p es => { p with employees := es })

private def budgetLens : Lens' Project Nat :=
  lens' (fun p => p.budget) (fun p b => { p with budget := b })

private def projectsLens : Lens' Department (List Project) :=
  lens' (fun d => d.projects) (fun d ps => { d with projects := ps })

private def departmentsLens : Lens' Company (List Department) :=
  lens' (fun c => c.departments) (fun c ds => { c with departments := ds })

private def addressLens : Lens' Person (Option Address) :=
  lens' (fun p => p.address) (fun p a => { p with address := a })

private def ageLens : Lens' Person Nat :=
  lens' (fun p => p.age) (fun p a => { p with age := a })

private def membersLens : Lens' Team (List Person) :=
  lens' (fun t => t.members) (fun t ms => { t with members := ms })

/-! ## Prisms -/

private def emailPrism : Prism' Contact String :=
  prism (fun e => Contact.email e)
        (fun c => match c with
         | Contact.email e => Sum.inr e
         | _ => Sum.inl c)

private def phonePrism : Prism' Contact String :=
  prism (fun p => Contact.phone p)
        (fun c => match c with
         | Contact.phone p => Sum.inr p
         | _ => Sum.inl c)

private def somePrism {α : Type} : Prism' (Option α) α :=
  prism (fun a => some a)
        (fun o => match o with
         | some a => Sum.inr a
         | none => Sum.inl none)

private def domesticPrism : Prism' Address (String × String) :=
  prism (fun (s, c) => Address.domestic s c)
        (fun a => match a with
         | Address.domestic s c => Sum.inr (s, c)
         | _ => Sum.inl a)

private def internationalPrism : Prism' Address (String × String × String) :=
  prism (fun (s, c, co) => Address.international s c co)
        (fun a => match a with
         | Address.international s c co => Sum.inr (s, c, co)
         | _ => Sum.inl a)

/-! ## Traversals -/

-- Specialized traversals for each type to avoid type annotation burden
private def employeeTraversal : Traversal (List Employee) (List Employee) Employee Employee :=
  List.traversed

private def projectTraversal : Traversal (List Project) (List Project) Project Project :=
  List.traversed

private def departmentTraversal : Traversal (List Department) (List Department) Department Department :=
  List.traversed

private def personTraversal : Traversal (List Person) (List Person) Person Person :=
  List.traversed

-- Keep the polymorphic version for any remaining uses
private def listTraversal {α β : Type} : Traversal (List α) (List β) α β :=
  List.traversed

/-! ## Test Cases -/

/--
**Lens ∘ Traversal**: Navigate to a field, then traverse its elements.

This composition allows us to focus on a collection within a structure,
then modify all elements of that collection.
-/
private def case_lensTraversal : TestCase := {
  name := "Lens ∘ Traversal compositions",
  run := do
    let project := Project.mk "App Rewrite" 100000 [
      Employee.mk "Alice" 80000 (Contact.email "alice@example.com"),
      Employee.mk "Bob" 75000 (Contact.phone "555-1234"),
      Employee.mk "Carol" 90000 Contact.none
    ]

    -- Lens ∘ Traversal: Give everyone a 10% raise
    -- employeesLens focuses on the employee list
    -- employeeTraversal then traverses each employee
    -- salaryLens focuses on each employee's salary
    let raiseComposed : Traversal' Project Nat :=
      employeesLens ∘ employeeTraversal ∘ salaryLens
    let afterRaise : Project := Traversal.over' raiseComposed (fun s => s * 110 / 100) project

    -- Verify all salaries increased
    if afterRaise.employees[0]!.salary != 88000 then
      throw (IO.userError s!"Expected salary 88000, got {afterRaise.employees[0]!.salary}")
    if afterRaise.employees[1]!.salary != 82500 then
      throw (IO.userError s!"Expected salary 82500, got {afterRaise.employees[1]!.salary}")
    if afterRaise.employees[2]!.salary != 99000 then
      throw (IO.userError s!"Expected salary 99000, got {afterRaise.employees[2]!.salary}")

    -- Compare with imperative code:
    -- let mut newEmployees = []
    -- for emp in project.employees:
    --   newEmployees.push(Employee { salary: emp.salary * 110 / 100, ..emp })
    -- project.employees = newEmployees

    IO.println "✓ Lens ∘ Traversal: gave 10% raise to all employees"

    -- Another example: Clear all contact info
    let contactComposed : Traversal' Project Contact := employeesLens ∘ employeeTraversal ∘ contactLens
    let noContact : Project := Traversal.over' contactComposed (fun _ => Contact.none) project

    if !noContact.employees.all (fun e => e.contact == Contact.none) then
      throw (IO.userError "Expected all contacts to be none")
    IO.println "✓ Lens ∘ Traversal: cleared all contact information"
}

/--
**Traversal ∘ Prism**: Traverse a collection, then focus on specific variants.

This composition allows us to traverse a collection and only modify elements
that match a specific pattern (via the prism).
-/
private def case_traversalPrism : TestCase := {
  name := "Traversal ∘ Prism compositions",
  run := do
    let employees := [
      Employee.mk "Alice" 80000 (Contact.email "alice@example.com"),
      Employee.mk "Bob" 75000 (Contact.phone "555-1234"),
      Employee.mk "Carol" 90000 (Contact.email "carol@company.org"),
      Employee.mk "Dave" 85000 Contact.none
    ]

    -- Traversal ∘ Prism: Update only email contacts
    -- employeeTraversal traverses all employees
    -- contactLens focuses on each contact field
    -- emailPrism only matches email contacts
    -- Note: Traversal ∘ Lens ∘ Prism all supported
    let emailComposed : Traversal' (List Employee) String := employeeTraversal ∘ contactLens ∘ emailPrism
    let updated : List Employee := Traversal.over' emailComposed
      (fun (email : String) => email.replace "@example.com" "@newdomain.com") employees

    -- Only Alice's email should be updated
    match updated[0]!.contact with
    | Contact.email e =>
        if e != "alice@newdomain.com" then
          throw (IO.userError s!"Expected alice@newdomain.com, got {e}")
    | _ => throw (IO.userError "Expected email contact")

    -- Bob has phone (unchanged)
    if updated[1]!.contact != Contact.phone "555-1234" then
      throw (IO.userError "Bob's phone should be unchanged")

    -- Carol's email unchanged (different domain)
    match updated[2]!.contact with
    | Contact.email e =>
        if e != "carol@company.org" then
          throw (IO.userError s!"Expected carol@company.org, got {e}")
    | _ => throw (IO.userError "Expected email contact")

    IO.println "✓ Traversal ∘ Prism: updated only matching email contacts"

    -- Another example: uppercase all phone numbers
    let phoneComposed : Traversal' (List Employee) String := employeeTraversal ∘ contactLens ∘ phonePrism
    let phones : List Employee := Traversal.over' phoneComposed (fun p => "PHONE:" ++ p) employees

    match phones[1]!.contact with
    | Contact.phone p =>
        if p != "PHONE:555-1234" then
          throw (IO.userError s!"Expected PHONE:555-1234, got {p}")
    | _ => throw (IO.userError "Expected phone contact")

    IO.println "✓ Traversal ∘ Prism: modified only phone contacts"
}

/--
**Lens ∘ Prism ∘ Lens**: Navigate to a field, focus on a variant, then a subfield.

This shows a three-way composition where we navigate through structure,
optionally focus on a variant, then access a field within that variant.
-/
private def case_lensPrismLens : TestCase := {
  name := "Lens ∘ Prism ∘ Lens chains",
  run := do
    let team := Team.mk "Engineering" [
      Person.mk "Alice" 30 (some (Address.domestic "123 Main St" "Boston")),
      Person.mk "Bob" 35 (some (Address.international "456 High St" "London" "UK")),
      Person.mk "Carol" 28 none,
      Person.mk "Dave" 32 (some (Address.domestic "789 Oak Ave" "Seattle"))
    ]

    -- Lens ∘ Traversal ∘ Lens ∘ Prism ∘ Prism: Complex composition
    -- membersLens → List Person
    -- personTraversal → traverse each Person
    -- addressLens → Option Address
    -- somePrism → Address (if present)
    -- domesticPrism → (String × String) (if domestic)

    let domesticAddressComposed : Traversal' Team (String × String) :=
      membersLens ∘ personTraversal ∘ addressLens ∘ somePrism ∘ domesticPrism

    -- Update all domestic addresses to add "USA"
    -- This only affects Alice and Dave, not Bob (international) or Carol (none)
    let withCountry : Team := Traversal.over' domesticAddressComposed
      (fun (pair : String × String) => (pair.1, pair.2 ++ ", USA")) team

    -- Verify Alice's address updated
    match withCountry.members[0]!.address with
    | some (Address.domestic s c) =>
        if s != "123 Main St" then
          throw (IO.userError s!"Expected '123 Main St', got {s}")
        if c != "Boston, USA" then
          throw (IO.userError s!"Expected 'Boston, USA', got {c}")
    | _ => throw (IO.userError "Expected domestic address")

    -- Bob's international address unchanged
    match withCountry.members[1]!.address with
    | some (Address.international _ c _) =>
        if c != "London" then
          throw (IO.userError s!"Expected 'London', got {c}")
    | _ => throw (IO.userError "Expected international address")

    -- Carol has no address (unchanged)
    if withCountry.members[2]!.address != none then
      throw (IO.userError "Carol should have no address")

    -- Dave's address updated
    match withCountry.members[3]!.address with
    | some (Address.domestic s c) =>
        if s != "789 Oak Ave" then
          throw (IO.userError s!"Expected '789 Oak Ave', got {s}")
        if c != "Seattle, USA" then
          throw (IO.userError s!"Expected 'Seattle, USA', got {c}")
    | _ => throw (IO.userError "Expected domestic address")

    IO.println "✓ Lens ∘ Prism ∘ Lens: updated nested optional variant fields"

    -- Compare with imperative code:
    -- let mut newMembers = []
    -- for person in team.members:
    --   match person.address:
    --     Some(Address.domestic(s, c)) =>
    --       newMembers.push(Person {
    --         address: Some(Address.domestic(s, c + ", USA")),
    --         ..person
    --       })
    --     _ => newMembers.push(person)
    -- team.members = newMembers
}

/--
**Deep Heterogeneous Chains**: Very deep compositions mixing all optic types.

Demonstrates that complex real-world data structures can be navigated
and updated through deeply composed optics without manual traversal code.
-/
private def case_deepChains : TestCase := {
  name := "Deep heterogeneous chains",
  run := do
    let company := Company.mk "TechCorp" [
      Department.mk "Engineering" [
        Project.mk "Backend" 500000 [
          Employee.mk "Alice" 100000 (Contact.email "alice@tech.com"),
          Employee.mk "Bob" 95000 (Contact.phone "555-0001")
        ],
        Project.mk "Frontend" 400000 [
          Employee.mk "Carol" 105000 (Contact.email "carol@tech.com"),
          Employee.mk "Dave" 90000 Contact.none
        ]
      ],
      Department.mk "Sales" [
        Project.mk "Enterprise" 300000 [
          Employee.mk "Eve" 85000 (Contact.email "eve@tech.com"),
          Employee.mk "Frank" 80000 (Contact.phone "555-0002")
        ]
      ]
    ]

    -- Deep composition: Company → Departments → Projects → Employees → Salary
    -- This is a 5-level deep traversal through nested structures
    let allSalariesComposed : Traversal' Company Nat :=
      departmentsLens ∘ departmentTraversal ∘
      projectsLens ∘ projectTraversal ∘
      employeesLens ∘ employeeTraversal ∘
      salaryLens

    -- Give everyone a 15% raise
    let afterRaise : Company := Traversal.over' allSalariesComposed (fun s => s * 115 / 100) company

    -- Verify specific employees got raises
    let alice := afterRaise.departments[0]!.projects[0]!.employees[0]!
    if alice.salary != 115000 then
      throw (IO.userError s!"Expected Alice salary 115000, got {alice.salary}")

    let carol := afterRaise.departments[0]!.projects[1]!.employees[0]!
    if carol.salary != 120750 then
      throw (IO.userError s!"Expected Carol salary 120750, got {carol.salary}")

    let eve := afterRaise.departments[1]!.projects[0]!.employees[0]!
    if eve.salary != 97750 then
      throw (IO.userError s!"Expected Eve salary 97750, got {eve.salary}")

    IO.println "✓ Deep chain: updated salaries across 5 levels of nesting"

    -- Another deep chain: Update only email contacts in high-budget projects
    let highBudgetEmailsComposed : Traversal' Company String :=
      departmentsLens ∘ departmentTraversal ∘
      projectsLens ∘ projectTraversal ∘
      employeesLens ∘ employeeTraversal ∘
      contactLens ∘ emailPrism

    let updated : Company := Traversal.over' highBudgetEmailsComposed
      (fun (email : String) => email.replace "@tech.com" "@techcorp.com") company

    -- Verify Alice's email updated
    match updated.departments[0]!.projects[0]!.employees[0]!.contact with
    | Contact.email e =>
        if e != "alice@techcorp.com" then
          throw (IO.userError s!"Expected alice@techcorp.com, got {e}")
    | _ => throw (IO.userError "Expected email contact")

    -- Bob's phone unchanged
    if updated.departments[0]!.projects[0]!.employees[1]!.contact !=
       Contact.phone "555-0001" then
      throw (IO.userError "Bob's phone should be unchanged")

    IO.println "✓ Deep chain: updated emails through 6 levels of nesting"

    -- Imperative equivalent would require 4+ nested loops:
    -- for dept in company.departments:
    --   for project in dept.projects:
    --     for employee in project.employees:
    --       match employee.contact:
    --         Contact.email(e) => employee.contact = Contact.email(e.replace(...))
    --         _ => ()
}

/--
**Type Inference**: Verify that complex compositions work without manual annotations.

Demonstrates that Lean's type inference correctly determines the optic type
resulting from heterogeneous compositions.
-/
private def case_typeInference : TestCase := {
  name := "Type inference across compositions",
  run := do
    let project := Project.mk "Test" 100000 [
      Employee.mk "Alice" 80000 (Contact.email "alice@test.com"),
      Employee.mk "Bob" 75000 (Contact.phone "555-1234")
    ]

    -- Minimal type annotations help type inference
    -- Lean infers this is a Traversal
    let composed1 : Traversal' Project Nat := employeesLens ∘ employeeTraversal ∘ salaryLens
    let result1 : Project := Traversal.over' composed1 (· + 5000) project
    if result1.employees[0]!.salary != 85000 then
      throw (IO.userError s!"Expected salary 85000, got {result1.employees[0]!.salary}")

    IO.println "✓ Type inference: Lens ∘ Traversal ∘ Lens → Traversal"

    -- This composition includes a Prism, so it's still a Traversal
    let composed2 : Traversal' Project String := employeesLens ∘ employeeTraversal ∘ contactLens ∘ emailPrism
    let result2 : Project := Traversal.over' composed2 (fun (s : String) => s ++ " (work)") project

    match result2.employees[0]!.contact with
    | Contact.email e =>
        if e != "alice@test.com (work)" then
          throw (IO.userError s!"Expected 'alice@test.com (work)', got {e}")
    | _ => throw (IO.userError "Expected email contact")

    IO.println "✓ Type inference: Lens ∘ Traversal ∘ Lens ∘ Prism → Traversal"

    -- The type system correctly determines the most specific optic type
    -- Lens ∘ Lens = Lens
    -- Lens ∘ Traversal = Traversal
    -- Traversal ∘ Prism = Traversal
    -- This follows the subtyping hierarchy: Iso > Lens > Prism > Traversal
}

/--
**Real-World Scenario**: Complete example with multiple operations.

Shows how heterogeneous compositions enable clean, declarative updates
to complex nested data structures in a single pipeline.
-/
private def case_realWorldScenario : TestCase := {
  name := "Real-world scenario: company reorganization",
  run := do
    let company := Company.mk "StartupInc" [
      Department.mk "Product" [
        Project.mk "MVP" 200000 [
          Employee.mk "Alice" 90000 (Contact.email "alice@startup.com"),
          Employee.mk "Bob" 85000 (Contact.email "bob@startup.com"),
          Employee.mk "Carol" 95000 (Contact.phone "555-0001")
        ]
      ],
      Department.mk "Growth" [
        Project.mk "Marketing" 150000 [
          Employee.mk "Dave" 80000 (Contact.email "dave@startup.com"),
          Employee.mk "Eve" 75000 Contact.none
        ]
      ]
    ]

    -- Step 1: Give 20% raise to all employees (company-wide)
    let allSalaries : Traversal' Company Nat :=
      departmentsLens ∘ departmentTraversal ∘
      projectsLens ∘ projectTraversal ∘
      employeesLens ∘ employeeTraversal ∘
      salaryLens
    let afterRaises : Company := Traversal.over' allSalaries (fun s => s * 120 / 100) company

    -- Step 2: Update email domain for all email contacts
    let allEmails : Traversal' Company String :=
      departmentsLens ∘ departmentTraversal ∘
      projectsLens ∘ projectTraversal ∘
      employeesLens ∘ employeeTraversal ∘
      contactLens ∘ emailPrism
    let newDomain : Company := Traversal.over' allEmails
                     (fun (e : String) => e.replace "@startup.com" "@bigcorp.com") afterRaises

    -- Step 3: Double budget for all projects
    let allBudgets : Traversal' Company Nat :=
      departmentsLens ∘ departmentTraversal ∘
      projectsLens ∘ projectTraversal ∘
      budgetLens
    let final : Company := Traversal.over' allBudgets (· * 2) newDomain

    -- Verify all changes applied correctly
    let alice := final.departments[0]!.projects[0]!.employees[0]!
    if alice.salary != 108000 then  -- 90000 * 1.2
      throw (IO.userError s!"Expected Alice salary 108000, got {alice.salary}")
    match alice.contact with
    | Contact.email e =>
        if e != "alice@bigcorp.com" then
          throw (IO.userError s!"Expected alice@bigcorp.com, got {e}")
    | _ => throw (IO.userError "Expected email contact")

    let mvpBudget := final.departments[0]!.projects[0]!.budget
    if mvpBudget != 400000 then  -- 200000 * 2
      throw (IO.userError s!"Expected budget 400000, got {mvpBudget}")

    let carol := final.departments[0]!.projects[0]!.employees[2]!
    if carol.salary != 114000 then  -- 95000 * 1.2
      throw (IO.userError s!"Expected Carol salary 114000, got {carol.salary}")
    if carol.contact != Contact.phone "555-0001" then  -- Phone unchanged
      throw (IO.userError "Expected Carol's phone to be unchanged")

    IO.println "✓ Real-world: applied company-wide reorganization with 3 optics pipelines"

    -- The imperative equivalent would be:
    -- 1. Multiple nested loops for each operation
    -- 2. Careful bookkeeping to avoid mutating while iterating
    -- 3. Much more code and higher bug potential
}

/-! ## Test Registration -/

def cases : List TestCase := [
  case_lensTraversal,
  case_traversalPrism,
  case_lensPrismLens,
  case_deepChains,
  case_typeInference,
  case_realWorldScenario
]

end CollimatorTests.AdvancedShowcase.HeterogeneousCompositions
