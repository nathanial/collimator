
import Collimator.Core
namespace Collimator.Concrete

open Collimator.Core


/--
`Tagged α β` stores only the output value `β` and ignores `α`.
-/
abbrev Tagged (_α : Type u) (β : Type u) := β

instance instProfunctorTagged :
    Profunctor (fun α : Type u => fun β : Type u => Tagged α β) where
  dimap _ post b := post b

instance instChoiceTagged :
    Choice (fun α : Type u => fun β : Type u => Tagged α β) where
  left := fun {α β _γ} (b : Tagged α β) => Sum.inl b
  right := fun {α β _γ} (b : Tagged α β) => Sum.inr b

end Collimator.Concrete
