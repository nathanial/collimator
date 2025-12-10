import Collimator.Optics.Prism
import Collimator.Optics.Lens
import Collimator.Combinators.Indexed

namespace Collimator.Instances.Option

open Collimator
open Collimator.Indexed
open Collimator.Core


/-- Prism focusing the value of an option when present (polymorphic version). -/
@[inline] def somePrism {α β : Type} : Prism (Option α) (Option β) α β :=
  fun {P} [Profunctor P] hChoice pab =>
    let _ : Choice P := hChoice
    let right := Choice.right (P := P) (γ := Option β) pab
    let split : Option α → Sum (Option β) α :=
      fun s => match s with
        | .some a => Sum.inr a
        | .none => Sum.inl (Option.none : Option β)
    let post : Sum (Option β) β → Option β :=
      fun s => match s with
        | Sum.inl opt => opt
        | Sum.inr b => Option.some b
    Profunctor.dimap (P := P) split post right

/-- Monomorphic version of somePrism for easier use in compositions.

Usage in compositions:
```lean
-- Clean syntax with monomorphic version
ofPrism (somePrism' Employee)

-- vs polymorphic version requiring both type parameters
ofPrism (somePrism (α := Employee) (β := Employee))
```
-/
@[inline] def somePrism' (α : Type) : Prism' (Option α) α :=
  somePrism

instance instHasAtOption {α : Type} : HasAt Unit (Option α) α where
  focus _ :=
    lens' (fun o => o) (fun _ replacement => replacement)

end Collimator.Instances.Option
