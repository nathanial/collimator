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

/-! ## Composed Optics using ⊚ operator -/

-- Employee → city (Lens ⊚ Lens = Lens)
def Employee.cityLens : Lens' Employee String :=
  Employee.addressLens ⊚ Address.cityLens

-- Department → all employee salaries
-- (Use explicit composition for Lens ⊚ Traversal ⊚ Lens chains)
def Department.allSalaries : Traversal' Department Int :=
  composeTraversal (composeLensTraversal Department.employeesLens traversed) (lensToTraversal Employee.salaryLens)

-- Company → all employees
def Company.allEmployees : Traversal' Company Employee :=
  composeTraversal (composeLensTraversal Company.departmentsLens traversed) (composeLensTraversal Department.employeesLens traversed)

-- Company → all employee cities
def Company.allCities : Traversal' Company String :=
  composeTraversal Company.allEmployees (lensToTraversal Employee.cityLens)

/-! ## Optic Information Commands

Hover over these to see output in the infoview panel.
-/

-- What is a Lens? What can it do?
#optic_info Lens

-- What is a Prism? (for sum types like Option, Result)
#optic_info Prism

-- What happens when we compose Lens with Traversal?
#optic_info Traversal

-- AffineTraversal: 0-or-1 focus (Lens ⊚ Prism)
#optic_info AffineTraversal

-- The full composition matrix
#optic_matrix

-- Capability comparison
#optic_caps Lens
#optic_caps Prism
#optic_caps Traversal
#optic_caps AffineTraversal

/-! ## Tracing Compositions

These show how optic types flow through composition chains.
-/

#eval traceComposition [
  ("Employee.addressLens", "Lens"),
  ("Address.cityLens", "Lens")
]
-- Result: Lens (Lens ∘ Lens = Lens)

#eval traceComposition [
  ("Department.employeesLens", "Lens"),
  ("traversed", "Traversal"),
  ("Employee.salaryLens", "Lens")
]
-- Result: Traversal (once you compose with Traversal, you stay Traversal)

#eval traceComposition [
  ("Company.departmentsLens", "Lens"),
  ("traversed", "Traversal"),
  ("Department.employeesLens", "Lens"),
  ("traversed", "Traversal"),
  ("Employee.addressLens", "Lens"),
  ("Address.zipLens", "Lens")
]
-- Result: Traversal (6-level deep composition!)

#eval traceComposition [
  ("userLens", "Lens"),
  ("maybeBioLens", "Lens"),
  ("somePrism", "Prism")
]
-- Result: AffineTraversal (Lens ∘ Prism = AffineTraversal, 0-or-1 focus)

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

-- Collect all cities in the company using the traversal
#eval! Fold.toListTraversal Company.allCities acme

-- Give everyone a 10% raise and show new salaries
#eval! (Traversal.over' Company.allEmployees (fun e => { e with salary := e.salary + e.salary / 10 }) acme).departments.map (·.employees.map (·.salary))
