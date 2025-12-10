import Collimator.Prelude
import Collimator.Commands
import Collimator.Tracing

/-!
# Tooling Demo

A practical example showing how to use Collimator's debugging and introspection tools.
Open this file in VS Code with the Lean extension to see output in the infoview.
-/

open Collimator
open Collimator.Tracing
open Collimator.Instances.List
open Collimator.Combinators
open scoped Collimator.Operators

/-! ## Data Model -/

structure Address where
  street : String
  city : String
  zip : String
deriving Repr, BEq

structure Employee where
  name : String
  salary : Int
  address : Address
deriving Repr, BEq

structure Department where
  name : String
  budget : Int
  employees : List Employee
deriving Repr, BEq

structure Company where
  name : String
  departments : List Department
deriving Repr, BEq

/-! ## Lenses -/

def Address.streetLens : Lens' Address String :=
  lens' (·.street) (fun a s => { a with street := s })

def Address.cityLens : Lens' Address String :=
  lens' (·.city) (fun a c => { a with city := c })

def Address.zipLens : Lens' Address String :=
  lens' (·.zip) (fun a z => { a with zip := z })

def Employee.nameLens : Lens' Employee String :=
  lens' (·.name) (fun e n => { e with name := n })

def Employee.salaryLens : Lens' Employee Int :=
  lens' (·.salary) (fun e s => { e with salary := s })

def Employee.addressLens : Lens' Employee Address :=
  lens' (·.address) (fun e a => { e with address := a })

def Department.nameLens : Lens' Department String :=
  lens' (·.name) (fun d n => { d with name := n })

def Department.budgetLens : Lens' Department Int :=
  lens' (·.budget) (fun d b => { d with budget := b })

def Department.employeesLens : Lens' Department (List Employee) :=
  lens' (·.employees) (fun d es => { d with employees := es })

def Company.nameLens : Lens' Company String :=
  lens' (·.name) (fun c n => { c with name := n })

def Company.departmentsLens : Lens' Company (List Department) :=
  lens' (·.departments) (fun c ds => { c with departments := ds })

/-! ## Composed Optics -/

-- Lens ⊚ Lens = Lens (works with the operator!)
def Employee.cityLens : Lens' Employee String :=
  Employee.addressLens ⊚ Address.cityLens

-- For heterogeneous composition, use explicit functions
def Department.employeesTraversal : Traversal' Department Employee :=
  composeLensTraversal Department.employeesLens traversed

def Company.allEmployees : Traversal' Company Employee :=
  composeTraversal
    (composeLensTraversal Company.departmentsLens traversed)
    (composeLensTraversal Department.employeesLens traversed)

/-! ## Type-Safe Composition Tracing

These use actual optics, not strings! The type system tells us what we're composing.
-/

-- Two lenses compose to a lens
#eval traceCompose₂ Employee.addressLens Address.cityLens

-- Lens + Traversal = Traversal
#eval traceCompose₂ Department.employeesLens (traversed : Traversal' (List Employee) Employee)

-- Three optics: Lens ⊚ Traversal ⊚ Lens = Traversal
#eval traceCompose₃ Department.employeesLens (traversed : Traversal' (List Employee) Employee) Employee.salaryLens

-- Four optics deep
#eval traceCompose₄
  Company.departmentsLens
  (traversed : Traversal' (List Department) Department)
  Department.employeesLens
  (traversed : Traversal' (List Employee) Employee)

-- Five optics: Company → all employee cities
#eval traceCompose₅
  Company.departmentsLens
  (traversed : Traversal' (List Department) Department)
  Department.employeesLens
  (traversed : Traversal' (List Employee) Employee)
  Employee.addressLens

-- Describe what an optic can do
#eval describeOpticInstance Employee.addressLens
#eval describeOpticInstance (traversed : Traversal' (List Int) Int)

/-! ## Optic Information Commands

Hover over these to see output in the infoview panel.
-/

#optic_info Lens
#optic_info Prism
#optic_info Traversal
#optic_info AffineTraversal

#optic_matrix

#optic_caps Lens
#optic_caps Prism
#optic_caps Traversal

/-! ## Sample Data -/

def acme : Company := {
  name := "Acme Corp"
  departments := [
    { name := "Engineering"
      budget := 1000000
      employees := [
        { name := "Alice", salary := 120000, address := { street := "123 Main", city := "Boston", zip := "02101" } },
        { name := "Bob", salary := 110000, address := { street := "456 Oak", city := "Cambridge", zip := "02139" } }
      ]
    },
    { name := "Sales"
      budget := 500000
      employees := [
        { name := "Carol", salary := 95000, address := { street := "789 Elm", city := "Boston", zip := "02102" } }
      ]
    }
  ]
}

/-! ## Using the Optics -/

-- View through a composed lens (Employee → city)
#eval view' Employee.cityLens { name := "Test", salary := 50000, address := { street := "1 St", city := "NYC", zip := "10001" } }

-- View a direct field
#eval view' Company.nameLens acme

-- Give everyone a 10% raise and show new salaries
#eval! (Traversal.over' Company.allEmployees (fun e => { e with salary := e.salary + e.salary / 10 }) acme).departments.map (·.employees.map (·.salary))
