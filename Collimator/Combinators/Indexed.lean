import Collimator.Optics.Types
import Collimator.Optics.Traversal
import Collimator.Optics.Lens

namespace Collimator.Indexed

open Collimator


/--
Capability for focusing a single position identified by an index.
-/
class HasIx (ι : Type) (s : Type) (a : Type) where
  ix : ι → Traversal' s a

/--
Capability for viewing or updating an optional focus at an index.
-/
class HasAt (ι : Type) (s : Type) (a : Type) where
  focus : ι → Lens' s (Option a)

/--
Retrieve the traversal focusing a particular index.
-/
@[inline] def ix {ι : Type} {s : Type} {a : Type}
    [HasIx ι s a] (i : ι) : Traversal' s a :=
  HasIx.ix i

/--
Retrieve the lens exposing an optional focus at a particular index.
-/
@[inline] def atLens {ι : Type} {s : Type} {a : Type}
    [HasAt ι s a] (i : ι) : Lens' s (Option a) :=
  HasAt.focus i

end Collimator.Indexed
