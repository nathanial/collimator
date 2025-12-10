import Lean
import Collimator.Tracing

/-!
# Collimator Commands

Custom commands for optics development and debugging.

## Available Commands

- `#optic_info <type>` - Print information about an optic type
- `#optic_matrix` - Print the composition matrix
- `#optic_caps <type>` - Print capabilities for an optic type

## Usage

```lean
import Collimator.Commands

#optic_info Lens
#optic_info Prism
#optic_matrix
```
-/

namespace Collimator.Commands

open Lean Elab Command Meta
open Collimator.Tracing

/--
`#optic_info <type>` prints comprehensive information about an optic type.

Example:
```
#optic_info Lens
```

Outputs description, use cases, and supported operations.
-/
syntax (name := opticInfoCmd) "#optic_info " ident : command

@[command_elab opticInfoCmd]
def elabOpticInfo : CommandElab := fun stx => do
  match stx with
  | `(#optic_info $id:ident) =>
    let name := id.getId.toString
    let info := describeOptic name
    let caps := getCapabilities name
    let capsStr := capabilitiesToString caps

    logInfo m!"========================================\n\
               Optic: {name}\n\
               ========================================\n\n\
               {info}\n\n\
               Supported operations: {capsStr}"
  | _ => throwUnsupportedSyntax

/--
`#optic_matrix` prints the optic composition result matrix.

Shows what type results from composing any two optic types.
-/
syntax (name := opticMatrixCmd) "#optic_matrix" : command

@[command_elab opticMatrixCmd]
def elabOpticMatrix : CommandElab := fun _ => do
  let types := #["Iso", "Lens", "Prism", "AffineTraversal", "Traversal"]

  let mut lines := #["Optic Composition Matrix",
                     "========================",
                     "",
                     "When you compose (outer ⊚ inner), the result type is:",
                     "",
                     "outer \\ inner | Iso    Lens   Prism  Affine Trav",
                     "--------------+------------------------------------"]

  for outer in types do
    let abbrevOuter := match outer with
      | "AffineTraversal" => "Affine       "
      | "Traversal" => "Trav         "
      | "Prism" => "Prism        "
      | "Lens" => "Lens         "
      | "Iso" => "Iso          "
      | x => x
    let cells := types.map fun inner =>
      let result := composeTypes outer inner
      match result with
      | "AffineTraversal" => "Affine"
      | "Traversal" => "Trav  "
      | "Prism" => "Prism "
      | "Lens" => "Lens  "
      | "Iso" => "Iso   "
      | x => x
    lines := lines.push s!"{abbrevOuter} | {String.intercalate " " cells.toList}"

  logInfo m!"{String.intercalate "\n" lines.toList}"

/--
`#optic_caps <type>` prints the capability matrix for an optic type.
-/
syntax (name := opticCapsCmd) "#optic_caps " ident : command

@[command_elab opticCapsCmd]
def elabOpticCaps : CommandElab := fun stx => do
  match stx with
  | `(#optic_caps $id:ident) =>
    let name := id.getId.toString
    let caps := getCapabilities name
    let checkMark := fun b => if b then "  Y  " else "  -  "

    logInfo m!"{name} capabilities:\n\
               Operation   | Avail\n\
               ------------|------\n\
               view        |{checkMark caps.view}\n\
               set         |{checkMark caps.set}\n\
               over        |{checkMark caps.over}\n\
               preview     |{checkMark caps.preview}\n\
               review      |{checkMark caps.review}\n\
               traverse    |{checkMark caps.traverse}\n\
               toList      |{checkMark caps.toList}"
  | _ => throwUnsupportedSyntax

end Collimator.Commands
