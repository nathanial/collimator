import Lean
import Collimator.Optics

/-!
# Automatic Lens Generation

This module provides a `makeLenses` command that automatically generates
lens definitions for all fields of a structure.

## Basic Usage

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

## Advanced Options

### Selective Generation

Generate lenses for only specific fields:

```lean
makeLenses Person (only := [name])
-- Only generates: personName
```

Exclude specific fields:

```lean
makeLenses Person (except := [age])
-- Generates all except: personAge
```

### Custom Naming

Add a custom prefix to lens names:

```lean
makeLenses Person (namePrefix := "lens")
-- Generates: lensPersonName, lensPersonAge
```

Add a custom suffix to lens names:

```lean
makeLenses Person (nameSuffix := "L")
-- Generates: personNameL, personAgeL
```

Combine options:

```lean
makeLenses Person (only := [name], namePrefix := "get")
-- Generates: getPersonName
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

/-! ## Syntax Definitions -/

/-- Option for selecting specific fields -/
syntax makeLensesOnlyOpt := "only" ":=" "[" ident,* "]"

/-- Option for excluding specific fields -/
syntax makeLensesExceptOpt := "except" ":=" "[" ident,* "]"

/-- Option for custom prefix -/
syntax makeLensesPrefixOpt := "namePrefix" ":=" str

/-- Option for custom suffix -/
syntax makeLensesSuffixOpt := "nameSuffix" ":=" str

/-- A single makeLenses option -/
syntax makeLensesOpt := makeLensesOnlyOpt <|> makeLensesExceptOpt <|> makeLensesPrefixOpt <|> makeLensesSuffixOpt

/-- Main syntax: makeLenses StructName (options...) -/
syntax "makeLenses" ident ("(" makeLensesOpt,* ")")? : command

/-! ## Helper Functions -/

/-- Helper to modify the first character of a string -/
private def modifyFirstChar (f : Char → Char) (s : String) : String :=
  match s.toList with
  | [] => s
  | c :: cs => String.ofList (f c :: cs)

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
      modifyFirstChar Char.toLower s
    else
      -- Multiple leading uppercase (e.g., "UIState") - lowercase all but keep the last one
      -- if it's followed by lowercase (e.g., "UI" + "State" ->  "ui" + "State")
      let _prefix := s.take (leadingUpperCount - 1)
      let suffix := s.drop (leadingUpperCount - 1)
      _prefix.toLower ++ suffix

/-- Helper to capitalize first letter -/
def toUpperFirst (s : String) : String :=
  if s.isEmpty then s
  else modifyFirstChar Char.toUpper s

/-- Configuration for makeLenses -/
structure MakeLensesConfig where
  /-- Only generate lenses for these fields (if non-empty) -/
  onlyFields : List Name := []
  /-- Exclude these fields from lens generation -/
  exceptFields : List Name := []
  /-- Prefix to add to lens names -/
  lensPrefix : String := ""
  /-- Suffix to add to lens names -/
  lensSuffix : String := ""

/-- Parse makeLenses options from syntax -/
def parseOptions (opts : Array (TSyntax `Collimator.Derive.makeLensesOpt)) : CommandElabM MakeLensesConfig := do
  let mut config : MakeLensesConfig := {}
  for opt in opts do
    match opt with
    | `(makeLensesOpt| only := [$ids,*]) =>
      config := { config with onlyFields := ids.getElems.toList.map (·.getId) }
    | `(makeLensesOpt| except := [$ids,*]) =>
      config := { config with exceptFields := ids.getElems.toList.map (·.getId) }
    | `(makeLensesOpt| namePrefix := $s:str) =>
      config := { config with lensPrefix := s.getString }
    | `(makeLensesOpt| nameSuffix := $s:str) =>
      config := { config with lensSuffix := s.getString }
    | _ => throwError "Unknown makeLenses option"
  return config

/-- Check if a field should be included based on config -/
def shouldIncludeField (config : MakeLensesConfig) (fieldName : Name) : Bool :=
  let passesOnly := config.onlyFields.isEmpty || config.onlyFields.contains fieldName
  let passesExcept := !config.exceptFields.contains fieldName
  passesOnly && passesExcept

/-- Generate the lens name for a field -/
def makeLensName (config : MakeLensesConfig) (structName : String) (fieldName : String) : String :=
  let base := toLowerFirst structName ++ toUpperFirst fieldName
  config.lensPrefix ++ base ++ config.lensSuffix

/-! ## Main Implementation -/

/-- Core implementation for generating lenses -/
def makeLensesCore (structName : Ident) (config : MakeLensesConfig) : CommandElabM Unit := do
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

  -- Validate 'only' fields exist
  for onlyField in config.onlyFields do
    unless fields.contains onlyField do
      throwError m!"makeLenses: Field '{onlyField}' specified in 'only' does not exist in '{structName}'.\n" ++
        m!"Available fields: {fields.toList}"

  -- Validate 'except' fields exist
  for exceptField in config.exceptFields do
    unless fields.contains exceptField do
      throwError m!"makeLenses: Field '{exceptField}' specified in 'except' does not exist in '{structName}'.\n" ++
        m!"Available fields: {fields.toList}"

  for fieldName in fields do
    -- Check if this field should be included
    unless shouldIncludeField config fieldName do
      continue

    -- Create lens name with prefix/suffix
    let structStr := declName.getString!
    let simpleLensName := makeLensName config structStr (fieldName.toString)
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

elab_rules : command
  | `(makeLenses $structName:ident) => do
    makeLensesCore structName {}
  | `(makeLenses $structName:ident ($opts:makeLensesOpt,*)) => do
    let config ← parseOptions opts.getElems
    makeLensesCore structName config

end Collimator.Derive
