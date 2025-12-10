import Collimator.Optics
import Collimator.Poly.Classes

namespace Collimator.Poly

open Collimator

/-- Getter supports view. -/
instance : HasView Getter where
  view g s := g.get s

end Collimator.Poly
