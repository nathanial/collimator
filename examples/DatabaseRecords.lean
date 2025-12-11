import Collimator.Prelude

/-!
# Database Records with Optics

This example shows how optics work with domain models typical of
database applications, including nested entities, optional fields,
and collection relationships.
-/

open Collimator
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

-- Path to phone number if present (using ∘ operator)
open Collimator.Instances.Option in
def contactPhoneNumber : AffineTraversal' ContactInfo String := contactPhone ∘ somePrism' String

-- Path to address city if present (chained composition with ∘)
open Collimator.Instances.Option in
def contactCity : AffineTraversal' ContactInfo String := contactAddress ∘ somePrism' Address ∘ addrCity

/-! ## Employee Lenses -/

def empId : Lens' Employee Nat := lens' (·.id) (fun e i => { e with id := i })
def empFirstName : Lens' Employee String := lens' (·.firstName) (fun e n => { e with firstName := n })
def empLastName : Lens' Employee String := lens' (·.lastName) (fun e n => { e with lastName := n })
def empTitle : Lens' Employee String := lens' (·.title) (fun e t => { e with title := t })
def empSalary : Lens' Employee Int := lens' (·.salary) (fun e s => { e with salary := s })
def empContact : Lens' Employee ContactInfo := lens' (·.contact) (fun e c => { e with contact := c })
def empManagerId : Lens' Employee (Option Nat) := lens' (·.managerId) (fun e m => { e with managerId := m })

-- Path to employee's email (composed with ∘)
def empEmail : Lens' Employee String := empContact ∘ contactEmail

/-! ## Department Lenses -/

def deptId : Lens' Department Nat := lens' (·.id) (fun d i => { d with id := i })
def deptName : Lens' Department String := lens' (·.name) (fun d n => { d with name := n })
def deptBudget : Lens' Department Int := lens' (·.budget) (fun d b => { d with budget := b })
def deptEmployees : Lens' Department (List Employee) := lens' (·.employees) (fun d e => { d with employees := e })

-- Traversal over all employees in department (using ∘)
def deptAllEmployees : Traversal' Department Employee :=
  deptEmployees ∘ Collimator.Instances.List.traversed

/-! ## Company Lenses -/

def coId : Lens' Company Nat := lens' (·.id) (fun c i => { c with id := i })
def coName : Lens' Company String := lens' (·.name) (fun c n => { c with name := n })
def coFounded : Lens' Company Nat := lens' (·.founded) (fun c f => { c with founded := f })
def coDepartments : Lens' Company (List Department) := lens' (·.departments) (fun c d => { c with departments := d })
def coHeadquarters : Lens' Company Address := lens' (·.headquarters) (fun c h => { c with headquarters := h })

-- Traversal over all departments (using ∘)
def coAllDepartments : Traversal' Company Department :=
  coDepartments ∘ Collimator.Instances.List.traversed

-- Traversal over all employees in company (using ∘)
def coAllEmployees : Traversal' Company Employee :=
  coAllDepartments ∘ deptAllEmployees

-- Traversal over all salaries (using ∘)
def coAllSalaries : Traversal' Company Int :=
  coAllEmployees ∘ empSalary

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

/-! ## Query Functions (using monomorphic fold API) -/

/-- Get all employee last names -/
def getAllEmployeeNames (company : Company) : List String :=
  company ^.. (coAllEmployees ∘ empLastName)

/-- Get total salary expense -/
def getTotalSalaries (company : Company) : Int :=
  (company ^.. coAllSalaries).foldl (· + ·) 0

/-- Get average salary -/
def getAverageSalary (company : Company) : Int :=
  let salaries := company ^.. coAllSalaries
  let total := salaries.foldl (· + ·) 0
  let count := salaries.length
  if count > 0 then total / count else 0

/-- Find employees earning above threshold -/
def highEarners (threshold : Int) (company : Company) : List Employee :=
  (company ^.. coAllEmployees).filter (·.salary > threshold)

/-- Get all departments with their employee counts -/
def deptSizes (company : Company) : List (String × Nat) :=
  (company ^.. coAllDepartments).map fun d => (d.name, d.employees.length)

/-! ## Update Functions (using monomorphic over/set) -/

/-- Give all employees a percentage raise -/
def giveRaise (percent : Int) (company : Company) : Company :=
  company & coAllSalaries %~ (fun s => s + s * percent / 100)

/-- Give raise to specific department using filtered traversal -/
def giveDeptRaise (deptNameFilter : String) (percent : Int) (company : Company) : Company :=
  let targetDeptSalaries : Traversal' Company Int :=
    filtered coAllDepartments (·.name == deptNameFilter) ∘ deptAllEmployees ∘ empSalary
  company & targetDeptSalaries %~ (fun s => s + s * percent / 100)

/-- Update company headquarters (using set with ∘) -/
def relocateHQ (newAddress : Address) (company : Company) : Company :=
  company & coHeadquarters .~ newAddress

/-- Standardize all email domains (using over with ∘) -/
def standardizeEmails (newDomain : String) (company : Company) : Company :=
  company & (coAllEmployees ∘ empEmail) %~
    (fun email =>
      let parts := email.splitOn "@"
      if parts.length >= 1 then parts[0]! ++ "@" ++ newDomain else email)

/-! ## Example Usage -/

def examples : IO Unit := do
  IO.println "=== Database Records Examples ==="
  IO.println ""

  -- Basic queries using ^. operators
  IO.println s!"Company: {sampleCompany ^. coName}"
  IO.println s!"Founded: {sampleCompany ^. coFounded}"
  IO.println s!"HQ City: {sampleCompany ^. (coHeadquarters ∘ addrCity)}"
  IO.println ""

  -- Employee queries using polymorphic fold functions
  IO.println "Employees:"
  let names := getAllEmployeeNames sampleCompany
  IO.println s!"  All last names: {names}"

  let total := getTotalSalaries sampleCompany
  IO.println s!"  Total salaries: ${total}"

  let avg := getAverageSalary sampleCompany
  IO.println s!"  Average salary: ${avg}"

  let count := (sampleCompany ^.. coAllEmployees).length
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

  -- Give raises using over
  let afterRaise := giveRaise 10 sampleCompany
  IO.println "After 10% raise:"
  IO.println s!"  New total salaries: ${getTotalSalaries afterRaise}"
  IO.println s!"  New average: ${getAverageSalary afterRaise}"
  IO.println ""

  -- Department-specific raise
  let afterEngRaise := giveDeptRaise "Engineering" 15 sampleCompany
  IO.println "After 15% raise for Engineering only:"
  let engDept := afterEngRaise.departments.find? (·.name == "Engineering")
  match engDept with
  | some d =>
    let salaries := d.employees.map (·.salary)
    IO.println s!"  Engineering salaries: {salaries}"
  | none => IO.println "  Engineering department not found"
  IO.println ""

  -- Optional field access using preview
  IO.println "Optional fields:"
  let employees := sampleCompany ^.. coAllEmployees
  match employees.head? with
  | some emp =>
    IO.println s!"  {emp.firstName}'s phone: {emp.contact ^? contactPhoneNumber}"
    IO.println s!"  {emp.firstName}'s city: {emp.contact ^? contactCity}"
  | none => IO.println "  No employees found"

  -- Check for employee without phone
  let bob := employees.find? (·.firstName == "Bob")
  match bob with
  | some emp =>
    IO.println s!"  Bob's phone: {emp.contact ^? contactPhoneNumber}"
  | none => pure ()

#eval examples
