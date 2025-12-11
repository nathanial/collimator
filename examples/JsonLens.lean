import Collimator.Prelude

/-!
# JSON Navigation with Optics

This example demonstrates how to use prisms and traversals to navigate
and modify JSON-like data structures in a type-safe manner.
-/

open Collimator
open Collimator.Core  -- For Profunctor, Strong, Choice (advanced usage)
open scoped Collimator.Operators

/-! ## JSON Value Type -/

/-- A simple JSON-like value type -/
inductive JsonValue where
  | null
  | bool (b : Bool)
  | number (n : Int)  -- Using Int for simplicity
  | string (s : String)
  | array (items : List JsonValue)
  | object (fields : List (String × JsonValue))
  deriving Repr, Inhabited

namespace JsonValue

/-! ## Prisms for Each Variant -/

/-- Focus on null values -/
def _null : Prism' JsonValue Unit :=
  prismFromPartial
    (fun | null => some () | _ => none)
    (fun () => null)

/-- Focus on boolean values -/
def _bool : Prism' JsonValue Bool :=
  prismFromPartial
    (fun | bool b => some b | _ => none)
    bool

/-- Focus on number values -/
def _number : Prism' JsonValue Int :=
  prismFromPartial
    (fun | number n => some n | _ => none)
    number

/-- Focus on string values -/
def _string : Prism' JsonValue String :=
  prismFromPartial
    (fun | string s => some s | _ => none)
    string

/-- Focus on array values -/
def _array : Prism' JsonValue (List JsonValue) :=
  prismFromPartial
    (fun | array items => some items | _ => none)
    array

/-- Focus on object values -/
def _object : Prism' JsonValue (List (String × JsonValue)) :=
  prismFromPartial
    (fun | object fields => some fields | _ => none)
    object

/-! ## Object Field Access -/

/-- Look up a field in a list of key-value pairs -/
def lookupField (key : String) (fields : List (String × JsonValue)) : Option JsonValue :=
  fields.find? (fun (k, _) => k == key) |>.map (·.2)

/-- Update a field in a list of key-value pairs -/
def updateField (key : String) (f : JsonValue → JsonValue)
    (fields : List (String × JsonValue)) : List (String × JsonValue) :=
  fields.map fun (k, v) => if k == key then (k, f v) else (k, v)

/-- AffineTraversal focusing on a specific field of a JSON object -/
def field (key : String) : AffineTraversal' JsonValue JsonValue :=
  fun {P} [Profunctor P] [Strong P] [Choice P] pab =>
    Profunctor.dimap
      (fun json =>
        match json with
        | object fields =>
          match lookupField key fields with
          | some v => Sum.inr (v, (json, key))
          | none => Sum.inl json
        | other => Sum.inl other)
      (fun
        | Sum.inl json => json
        | Sum.inr (newVal, (object fields, k)) => object (updateField k (fun _ => newVal) fields)
        | Sum.inr (_, (other, _)) => other)  -- shouldn't happen
      (Choice.right (Strong.first pab))

/-! ## Array Index Access -/

/-- AffineTraversal focusing on element at index in a JSON array -/
def index (i : Nat) : AffineTraversal' JsonValue JsonValue :=
  fun {P} [Profunctor P] [Strong P] [Choice P] pab =>
    Profunctor.dimap
      (fun json =>
        match json with
        | array items =>
          match items.get? i with
          | some v => Sum.inr (v, (items, i))
          | none => Sum.inl json
        | other => Sum.inl other)
      (fun
        | Sum.inl json => json
        | Sum.inr (newVal, (items, idx)) => array (items.set idx newVal))
      (Choice.right (Strong.first pab))

/-! ## Traversing All Array Elements -/

/-- Traversal over all elements in a JSON array -/
def elements : Traversal' JsonValue JsonValue :=
  _array ∘ Collimator.Instances.List.traversed

end JsonValue

/-! ## Example Usage -/

/-- Sample JSON-like data representing a user list -/
def sampleData : JsonValue :=
  .object [
    ("users", .array [
      .object [
        ("name", .string "Alice"),
        ("age", .number 30),
        ("active", .bool true)
      ],
      .object [
        ("name", .string "Bob"),
        ("age", .number 25),
        ("active", .bool false)
      ],
      .object [
        ("name", .string "Charlie"),
        ("age", .number 35),
        ("active", .bool true)
      ]
    ]),
    ("count", .number 3)
  ]

open JsonValue in
def examples : IO Unit := do
  IO.println "=== JSON Lens Examples ==="
  IO.println ""

  -- Access nested field: data.users[0].name
  let firstUserName : AffineTraversal' JsonValue String :=
    field "users" ∘ index 0 ∘ field "name" ∘ _string
  IO.println s!"First user name: {sampleData ^? firstUserName}"
  -- Output: First user name: some "Alice"

  -- Access count field
  let countPath : AffineTraversal' JsonValue Int := field "count" ∘ _number
  IO.println s!"Count: {sampleData ^? countPath}"
  -- Output: Count: some 3

  -- Modify: increment all ages by 1
  let allAges : Traversal' JsonValue Int :=
    field "users" ∘ elements ∘ field "age" ∘ _number
  let updated := sampleData & allAges %~ (· + 1)
  IO.println s!"After incrementing ages:"

  -- Verify first user's new age
  let firstAge : AffineTraversal' JsonValue Int :=
    field "users" ∘ index 0 ∘ field "age" ∘ _number
  IO.println s!"  Alice's new age: {updated ^? firstAge}"
  -- Output: Alice's new age: some 31

  -- Collect all names
  let allNames : Traversal' JsonValue String :=
    field "users" ∘ elements ∘ field "name" ∘ _string
  let names := sampleData ^.. allNames
  IO.println s!"All user names: {names}"
  -- Output: All user names: ["Alice", "Bob", "Charlie"]

  -- Check if any user is inactive
  let allActive : Traversal' JsonValue Bool :=
    field "users" ∘ elements ∘ field "active" ∘ _bool
  let anyInactive := Fold.anyOfTraversal allActive (· == false) sampleData
  IO.println s!"Any inactive users? {anyInactive}"
  -- Output: Any inactive users? true

  IO.println ""
  IO.println "=== Construction with review ==="

  -- Build JSON values using review
  let newUser := JsonValue.object [
    ("name", review' _string "Diana"),
    ("age", review' _number 28),
    ("active", review' _bool true)
  ]
  IO.println s!"New user: {repr newUser}"

-- #eval examples
