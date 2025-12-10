import Collimator.Optics
import Collimator.Poly.Classes

namespace Collimator.Poly

open Collimator

-- Review has a different type signature (t, b) vs the polymorphic (s, t, a, b)
-- We need a specialized class for Review since it's a 2-parameter type

/-- Standalone review function for the Review optic -/
def reviewR {t b : Type} (r : Review t b) (x : b) : t := r.build x

end Collimator.Poly
