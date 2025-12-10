import Collimator.Optics.Types
import Collimator.Concrete.FunArrow

namespace Collimator

open Collimator.Concrete


namespace Setter

/-- Modify the target of a setter. -/
def over' {s t a b : Type}
    (st : Setter s t a b) (f : a → b) : s → t :=
  let arrow := FunArrow.mk (α := a) (β := b) f
  let transformed := st (P := fun α β => FunArrow α β) arrow
  fun s => transformed s

/-- Replace the target of a setter with a constant value. -/
def set' {s t a b : Type}
    (st : Setter s t a b) (value : b) : s → t :=
  over' st (fun _ => value)

end Setter

end Collimator
