import Collimator.Poly
import Collimator.Optics.Fold
import Collimator.Combinators
import Collimator.Helpers

/-!
# Collimator Re-exports

This module re-exports commonly used functions from subnamespaces into the
main `Collimator` namespace, allowing users to simply `open Collimator` for
most use cases.
-/

namespace Collimator

-- Re-export polymorphic API from Collimator.Poly
export Collimator.Poly (view over set preview review traverse)

-- Re-export combinators from Collimator.Combinators
-- Note: With type-alias optics, standard function composition (∘) is used
-- instead of explicit compose functions.
export Collimator.Combinators (filtered filteredList ifilteredList)

-- Re-export helpers
export Collimator.Helpers (first' second' lensOf lensOfPoly prismOf some' each')

end Collimator
