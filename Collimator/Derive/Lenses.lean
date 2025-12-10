import Lean
import Collimator.Optics.Lens

/-!
# Automatic Lens Generation

This module provides a `makeLenses` command that automatically generates
lens definitions for all fields of a structure.

## Usage

```lean
-- File: MyTypes.lean
structure Person where
  name : String
  age : Nat

-- File: MyLenses.lean (separate file!)
import MyTypes
import Collimator.Derive.Lenses

open Collimator.Derive in
makeLenses Person

-- This automatically generates:
-- def personName : Lens' Person String := ...
-- def personAge : Lens' Person Nat := ...
```

## Important Limitation

**The `makeLenses` command MUST be used in a different file than where the
structure is defined.**

This is due to Lean 4's elaboration ordering: `getStructureFields` requires
the structure to be fully elaborated in the environment, which doesn't happen
until after the current file completes. Attempting to use `makeLenses` in the
same file as the structure definition will result in an error.

## When to Use This vs Manual Lenses

**Use `makeLenses` when:**
- You have many structures with many fields
- Structure and lens definitions can be in separate files
- You want to reduce boilerplate

**Use manual lens definitions when:**
- You want lenses in the same file as the structure
- You have only a few lenses to define
- You want more control over lens names or behavior

-/

namespace Collimator.Derive

open Lean Elab Command Meta

syntax "makeLenses" ident : command

/-- Helper to convert struct name to camelCase (lowercase all leading uppercase letters) -/
def toLowerFirst (s : String) : String :=
  if s.isEmpty then s
  else
    -- Find how many leading characters are uppercase
    let leadingUpperCount := s.toList.takeWhile Char.isUpper |>.length
    if leadingUpperCount == 0 then s
    else if leadingUpperCount == s.length then
      -- All uppercase - lowercase everything (e.g., "UI" -> "ui")
      s.toLower
    else if leadingUpperCount == 1 then
      -- Single uppercase letter - just lowercase it (e.g., "Window" -> "window")
      s.modify 0 Char.toLower
    else
      -- Multiple leading uppercase (e.g., "UIState") - lowercase all but keep the last one
      -- if it's followed by lowercase (e.g., "UI" + "State" ->  "ui" + "State")
      let _prefix := s.take (leadingUpperCount - 1)
      let suffix := s.drop (leadingUpperCount - 1)
      _prefix.toLower ++ suffix

/-- Helper to capitalize first letter -/
def toUpperFirst (s : String) : String :=
  if s.isEmpty then s
  else s.modify 0 Char.toUpper

elab_rules : command
  | `(makeLenses $structName:ident) => do
    let env ← getEnv

    -- Resolve the identifier with helpful error message
    let declName ← try
      liftCoreM <| Lean.resolveGlobalConstNoOverload structName
    catch _ =>
      throwError m!"makeLenses: Cannot find structure '{structName}'.\n\n" ++
        m!"Hint: The structure must be defined before calling makeLenses.\n" ++
        m!"If this structure is in the same file, you must move makeLenses " ++
        m!"to a separate file that imports this one.\n\n" ++
        m!"Example:\n" ++
        m!"  -- File: MyTypes.lean\n" ++
        m!"  structure {structName} where ...\n\n" ++
        m!"  -- File: MyLenses.lean\n" ++
        m!"  import MyTypes\n" ++
        m!"  makeLenses {structName}"

    -- Get the structure fields with validation
    let fields := getStructureFields env declName
    if fields.isEmpty then
      throwError m!"makeLenses: '{structName}' has no fields or is not a structure.\n" ++
        m!"Hint: makeLenses only works with structure types, not inductives or other definitions."

    for fieldName in fields do
      -- Create lens name: structName + FieldName (camelCase)
      -- Extract just the structure name (last component) from the fully qualified name
      let structStr := toLowerFirst (declName.getString!)
      let fieldStr := toUpperFirst (fieldName.toString)
      let simpleLensName := structStr ++ fieldStr
      -- Use simple name - the namespace context will handle qualification
      let lensName := Name.mkSimple simpleLensName
      let lensId := mkIdent lensName
      let fieldId := mkIdent fieldName

      -- Get the field type
      let projName := declName ++ fieldName
      let some projInfo := env.find? projName
        | throwError s!"Cannot find projection {projName}"

      let fieldType ← liftTermElabM <| Meta.forallTelescopeReducing projInfo.type fun _ body =>
        PrettyPrinter.delab body

      -- Generate the lens definition
      let cmd ← `(command|
        @[inline] def $lensId : Lens' $structName $fieldType :=
          lens' (·.$fieldId) (fun s v => { s with $fieldId:ident := v })
      )

      elabCommand cmd

end Collimator.Derive
