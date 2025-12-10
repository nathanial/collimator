/-!
# Database Records with Optics

This example shows how optics work with domain models typical of
database applications, including nested entities, optional fields,
and collection relationships.
-/

import Collimator.Prelude

open Collimator
open Collimator.Poly
open Collimator.Combinators
open scoped Collimator.Operators

/-! ## Domain Model -/

structure Address where
  street : String
  city : String
  state : String
  zipCode : String
  country : String := "USA"
  deriving Repr

structure ContactInfo where
  email : String
  phone : Option String
  address : Option Address
  deriving Repr

structure Employee where
  id : Nat
  firstName : String
  lastName : String
  title : String
  salary : Int
  contact : ContactInfo
  managerId : Option Nat
  deriving Repr

structure Department where
  id : Nat
  name : String
  budget : Int
  employees : List Employee
  deriving Repr

structure Company where
  id : Nat
  name : String
  founded : Nat
  departments : List Department
  headquarters : Address
  deriving Repr

/-! ## Address Lenses -/

def addrStreet : Lens' Address String := lens' (·.street) (fun a s => { a with street := s })
def addrCity : Lens' Address String := lens' (·.city) (fun a c => { a with city := c })
def addrState : Lens' Address String := lens' (·.state) (fun a s => { a with state := s })
def addrZip : Lens' Address String := lens' (·.zipCode) (fun a z => { a with zipCode := z })
def addrCountry : Lens' Address String := lens' (·.country) (fun a c => { a with country := c })

/-! ## ContactInfo Lenses -/

def contactEmail : Lens' ContactInfo String := lens' (·.email) (fun c e => { c with email := e })
def contactPhone : Lens' ContactInfo (Option String) := lens' (·.phone) (fun c p => { c with phone := p })
def contactAddress : Lens' ContactInfo (Option Address) := lens' (·.address) (fun c a => { c with address := a })

-- Path to phone number if present
open Collimator.Instances.Option in
def contactPhoneNumber : AffineTraversal' ContactInfo String := contactPhone ⊚ somePrism'

-- Path to address city if present
open Collimator.Instances.Option in
def contactCity : AffineTraversal' ContactInfo String := contactAddress ⊚ somePrism' ⊚ addrCity

/-! ## Employee Lenses -/

def empId : Lens' Employee Nat := lens' (·.id) (fun e i => { e with id := i })
def empFirstName : Lens' Employee String := lens' (·.firstName) (fun e n => { e with firstName := n })
def empLastName : Lens' Employee String := lens' (·.lastName) (fun e n => { e with lastName := n })
def empTitle : Lens' Employee String := lens' (·.title) (fun e t => { e with title := t })
def empSalary : Lens' Employee Int := lens' (·.salary) (fun e s => { e with salary := s })
def empContact : Lens' Employee ContactInfo := lens' (·.contact) (fun e c => { e with contact := c })
def empManagerId : Lens' Employee (Option Nat) := lens' (·.managerId) (fun e m => { e with managerId := m })

-- Computed: full name
def empFullName : Getter' Employee String :=
  ⟨fun {_P _R} [Profunctor _P] [_hS : Strong _P] [_hC : Choice _P] (pab : _P String String) =>
    Profunctor.dimap (fun e => e.firstName ++ " " ++ e.lastName) id pab⟩

-- Path to employee's email
def empEmail : Lens' Employee String := empContact ⊚ contactEmail

/-! ## Department Lenses -/

def deptId : Lens' Department Nat := lens' (·.id) (fun d i => { d with id := i })
def deptName : Lens' Department String := lens' (·.name) (fun d n => { d with name := n })
def deptBudget : Lens' Department Int := lens' (·.budget) (fun d b => { d with budget := b })
def deptEmployees : Lens' Department (List Employee) := lens' (·.employees) (fun d e => { d with employees := e })

-- Traversal over all employees in department
def deptAllEmployees : Traversal' Department Employee :=
  deptEmployees ⊚ Collimator.Instances.List.traversed

/-! ## Company Lenses -/

def coId : Lens' Company Nat := lens' (·.id) (fun c i => { c with id := i })
def coName : Lens' Company String := lens' (·.name) (fun c n => { c with name := n })
def coFounded : Lens' Company Nat := lens' (·.founded) (fun c f => { c with founded := f })
def coDepartments : Lens' Company (List Department) := lens' (·.departments) (fun c d => { c with departments := d })
def coHeadquarters : Lens' Company Address := lens' (·.headquarters) (fun c h => { c with headquarters := h })

-- Traversal over all departments
def coAllDepartments : Traversal' Company Department :=
  coDepartments ⊚ Collimator.Instances.List.traversed

-- Traversal over all employees in company
def coAllEmployees : Traversal' Company Employee :=
  coAllDepartments ⊚ deptAllEmployees

-- Traversal over all salaries
def coAllSalaries : Traversal' Company Int :=
  coAllEmployees ⊚ empSalary

/-! ## Sample Data -/

def sampleCompany : Company := {
  id := 1
  name := "TechCorp"
  founded := 2010
  headquarters := {
    street := "100 Main Street"
    city := "San Francisco"
    state := "CA"
    zipCode := "94105"
    country := "USA"
  }
  departments := [
    { id := 1
      name := "Engineering"
      budget := 5000000
      employees := [
        { id := 101
          firstName := "Alice"
          lastName := "Smith"
          title := "Senior Engineer"
          salary := 150000
          contact := {
            email := "alice@techcorp.com"
            phone := some "555-0101"
            address := some {
              street := "123 Oak St"
              city := "San Francisco"
              state := "CA"
              zipCode := "94102"
            }
          }
          managerId := none
        },
        { id := 102
          firstName := "Bob"
          lastName := "Jones"
          title := "Engineer"
          salary := 120000
          contact := {
            email := "bob@techcorp.com"
            phone := none
            address := none
          }
          managerId := some 101
        }
      ]
    },
    { id := 2
      name := "Sales"
      budget := 3000000
      employees := [
        { id := 201
          firstName := "Carol"
          lastName := "White"
          title := "Sales Director"
          salary := 130000
          contact := {
            email := "carol@techcorp.com"
            phone := some "555-0201"
            address := some {
              street := "456 Pine Ave"
              city := "Oakland"
              state := "CA"
              zipCode := "94612"
            }
          }
          managerId := none
        }
      ]
    }
  ]
}

/-! ## Query Functions -/

/-- Get all employee names -/
def getAllEmployeeNames (company : Company) : List String :=
  Fold.toList (coAllEmployees ⊚ empLastName) company

/-- Get total salary expense -/
def getTotalSalaries (company : Company) : Int :=
  Fold.sumOf coAllSalaries company

/-- Get average salary -/
def getAverageSalary (company : Company) : Int :=
  let total := Fold.sumOf coAllSalaries company
  let count := Fold.lengthOf coAllSalaries company
  if count > 0 then total / count else 0

/-- Find employees earning above threshold -/
def highEarners (threshold : Int) (company : Company) : List Employee :=
  Fold.toList (coAllEmployees ⊚ filtered (·.salary > threshold)) company

/-- Get all departments with their employee counts -/
def deptSizes (company : Company) : List (String × Nat) :=
  Fold.toList coAllDepartments company
    |>.map fun d => (d.name, d.employees.length)

/-! ## Update Functions -/

/-- Give all employees a percentage raise -/
def giveRaise (percent : Int) (company : Company) : Company :=
  over coAllSalaries (fun s => s + s * percent / 100) company

/-- Give raise to specific department -/
def giveDeptRaise (deptName : String) (percent : Int) (company : Company) : Company :=
  over (coAllDepartments ⊚ filtered (·.name == deptName) ⊚ deptAllEmployees ⊚ empSalary)
       (fun s => s + s * percent / 100)
       company

/-- Update company headquarters -/
def relocateHQ (newAddress : Address) (company : Company) : Company :=
  set coHeadquarters newAddress company

/-- Standardize all email domains -/
def standardizeEmails (newDomain : String) (company : Company) : Company :=
  over (coAllEmployees ⊚ empEmail)
       (fun email =>
         let parts := email.splitOn "@"
         if parts.length >= 1 then parts[0]! ++ "@" ++ newDomain else email)
       company

/-! ## Example Usage -/

def examples : IO Unit := do
  IO.println "=== Database Records Examples ==="
  IO.println ""

  -- Basic queries
  IO.println s!"Company: {sampleCompany ^. coName}"
  IO.println s!"Founded: {sampleCompany ^. coFounded}"
  IO.println s!"HQ City: {sampleCompany ^. coHeadquarters ⊚ addrCity}"
  IO.println ""

  -- Employee queries
  IO.println "Employees:"
  let names := getAllEmployeeNames sampleCompany
  IO.println s!"  All last names: {names}"

  let total := getTotalSalaries sampleCompany
  IO.println s!"  Total salaries: ${total}"

  let avg := getAverageSalary sampleCompany
  IO.println s!"  Average salary: ${avg}"

  let count := Fold.lengthOf coAllEmployees sampleCompany
  IO.println s!"  Employee count: {count}"
  IO.println ""

  -- Department queries
  IO.println "Departments:"
  for (name, size) in deptSizes sampleCompany do
    IO.println s!"  {name}: {size} employees"
  IO.println ""

  -- High earners
  let high := highEarners 125000 sampleCompany
  IO.println s!"Employees earning > $125k:"
  for emp in high do
    IO.println s!"  {emp.firstName} {emp.lastName}: ${emp.salary}"
  IO.println ""

  -- Give raises
  let afterRaise := giveRaise 10 sampleCompany
  IO.println "After 10% raise:"
  IO.println s!"  New total salaries: ${getTotalSalaries afterRaise}"
  IO.println s!"  New average: ${getAverageSalary afterRaise}"
  IO.println ""

  -- Department-specific raise
  let afterEngRaise := giveDeptRaise "Engineering" 15 sampleCompany
  IO.println "After 15% raise for Engineering only:"
  let engSalaries := Fold.toList (coAllDepartments ⊚ filtered (·.name == "Engineering")
                                   ⊚ deptAllEmployees ⊚ empSalary) afterEngRaise
  IO.println s!"  Engineering salaries: {engSalaries}"
  IO.println ""

  -- Optional field access
  IO.println "Optional fields:"
  let firstEmp := Fold.toList coAllEmployees sampleCompany |>.head?
  match firstEmp with
  | some emp =>
    IO.println s!"  {emp.firstName}'s phone: {emp ^? (empContact ⊚ contactPhoneNumber)}"
    IO.println s!"  {emp.firstName}'s city: {emp ^? (empContact ⊚ contactCity)}"
  | none => IO.println "  No employees found"

  -- Check for employee without phone
  let bob := Fold.toList (coAllEmployees ⊚ filtered (·.firstName == "Bob")) sampleCompany |>.head?
  match bob with
  | some emp =>
    IO.println s!"  Bob's phone: {emp ^? (empContact ⊚ contactPhoneNumber)}"
  | none => pure ()

-- #eval examples
