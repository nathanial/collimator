import Collimator.Optics
import Collimator.Poly.Classes

namespace Collimator.Poly

open Collimator

/-- Setter supports over. -/
instance : HasOver Setter where
  over st f s := Collimator.Setter.over' st f s

/-- Setter supports set. -/
instance : HasSet Setter where
  set st b s := Collimator.Setter.set' st b s

end Collimator.Poly
