import Collimator.Core
import Collimator.Optics
import Collimator.Concrete.Forget
import Collimator.Concrete.FunArrow
import Collimator.Combinators

/-!
# Lens Laws

This module formalizes and proves the three fundamental lens laws for profunctor optics:
1. **GetPut**: Viewing after setting gives you what you set
2. **PutGet**: Setting what you view doesn't change anything
3. **PutPut**: Setting twice is the same as setting once with the last value

## References
- Profunctor Optics: Modular Data Accessors (Pickering, Gibbons, Wu)
- ProfunctorOpticsDesign.md Phase 5
-/

namespace Collimator.Theorems

open Collimator
open Collimator.Core
open Collimator.Concrete


/--
A lawful lens requires the underlying get and set functions to satisfy three laws.
-/
class LawfulLens {s : Type} {a : Type}
    (get : s → a) (set : s → a → s) where
  /-- Getting after setting returns the value that was set. -/
  getput : ∀ (s : s) (v : a), get (set s v) = v
  /-- Setting the current value doesn't change anything. -/
  putget : ∀ (s : s), set s (get s) = s
  /-- Setting twice is the same as setting once with the last value. -/
  putput : ∀ (s : s) (v v' : a), set (set s v) v' = set s v'

/-! ## Helper Lemmas -/

/--
Unfolding lemma: `view` applied to a lens constructed from get/set is equivalent to get.
-/
theorem view_lens_eq {s a : Type} (get : s → a) (set : s → a → s) (x : s) :
    view' (lens' get set) x = get x := by
  unfold view' lens'
  -- view unfolds to applying the lens to the Forget profunctor
  simp [Profunctor.dimap, Strong.first]

/--
Unfolding lemma: `set` applied to a lens constructed from get/set is equivalent to the set function.
-/
theorem set_lens_eq {s a : Type} (get : s → a) (set : s → a → s) (v : a) (x : s) :
    set' (lens' get set) v x = set x v := by
  unfold set' over' lens'
  simp [Profunctor.dimap, Strong.first]

/-! ## Main Lens Laws -/

/--
**GetPut Law**: Viewing a lens after setting it returns the value that was set.

If `l = lens get set` and the underlying functions satisfy `get (set s v) = v`,
then `view l (set l v s) = v`.
-/
theorem lens_getput {s a : Type} (get : s → a) (set : s → a → s)
    (h : ∀ (s : s) (v : a), get (set s v) = v) :
    ∀ (s : s) (v : a), view' (lens' get set) (set' (lens' get set) v s) = v := by
  intro s v
  rw [set_lens_eq, view_lens_eq]
  exact h s v

/--
**PutGet Law**: Setting a lens to its current value doesn't change the structure.

If `l = lens get set` and the underlying functions satisfy `set s (get s) = s`,
then `set l (view l s) s = s`.
-/
theorem lens_putget {s a : Type} (get : s → a) (set : s → a → s)
    (h : ∀ (s : s), set s (get s) = s) :
    ∀ (s : s), set' (lens' get set) (view' (lens' get set) s) s = s := by
  intro s
  rw [view_lens_eq, set_lens_eq]
  exact h s

/--
**PutPut Law**: Setting a lens twice is the same as setting it once with the last value.

If `l = lens get set` and the underlying functions satisfy `set (set s v) v' = set s v'`,
then `set l v (set l v' s) = set l v s`.
-/
theorem lens_putput {s a : Type} (get : s → a) (set : s → a → s)
    (h : ∀ (s : s) (v v' : a), set (set s v) v' = set s v') :
    ∀ (s : s) (v v' : a), set' (lens' get set) v (set' (lens' get set) v' s) = set' (lens' get set) v s := by
  intro s v v'
  rw [set_lens_eq, set_lens_eq, set_lens_eq]
  exact h s v' v

/-! ## Bundled Lawful Lens Theorems -/

/--
If the underlying get/set functions form a lawful lens, then all three lens laws hold
for the profunctor lens constructed from them.
-/
theorem lawful_lens_satisfies_laws {s a : Type} (get : s → a) (set : s → a → s)
    [h : LawfulLens get set] :
    (∀ (s : s) (v : a), view' (lens' get set) (set' (lens' get set) v s) = v) ∧
    (∀ (s : s), set' (lens' get set) (view' (lens' get set) s) s = s) ∧
    (∀ (s : s) (v v' : a), set' (lens' get set) v (set' (lens' get set) v' s) = set' (lens' get set) v s) := by
  constructor
  · exact lens_getput get set h.getput
  constructor
  · exact lens_putget get set h.putget
  · exact lens_putput get set h.putput

/-! ## Lens Composition Laws -/

open Collimator.Combinators

/--
Helper: Extract getter from composed lenses.
-/
private def composed_get {s a u : Type}
    (get_outer : s → a) (get_inner : a → u) : s → u :=
  get_inner ∘ get_outer

/--
Helper: Extract setter from composed lenses.
-/
private def composed_set {s a u : Type}
    (get_outer : s → a) (set_outer : s → a → s)
    (set_inner : a → u → a) : s → u → s :=
  fun s u => set_outer s (set_inner (get_outer s) u)

/--
**Composition Preserves GetPut**: If two lenses are lawful, their composition is also lawful.
The getput law holds for composed lenses.
-/
theorem composeLens_preserves_getput {s a u : Type}
    (get_o : s → a) (set_o : s → a → s)
    (get_i : a → u) (set_i : a → u → a)
    [ho : LawfulLens get_o set_o] [hi : LawfulLens get_i set_i] :
    ∀ (s : s) (v : u),
      composed_get get_o get_i (composed_set get_o set_o set_i s v) = v := by
  intro s v
  unfold composed_get composed_set
  simp
  rw [ho.getput]
  exact hi.getput (get_o s) v

/--
**Composition Preserves PutGet**: The putget law holds for composed lenses.
-/
theorem composeLens_preserves_putget {s a u : Type}
    (get_o : s → a) (set_o : s → a → s)
    (get_i : a → u) (set_i : a → u → a)
    [ho : LawfulLens get_o set_o] [hi : LawfulLens get_i set_i] :
    ∀ (s : s),
      composed_set get_o set_o set_i s (composed_get get_o get_i s) = s := by
  intro s
  unfold composed_get composed_set
  simp
  rw [hi.putget]
  exact ho.putget s

/--
**Composition Preserves PutPut**: The putput law holds for composed lenses.
-/
theorem composeLens_preserves_putput {s a u : Type}
    (get_o : s → a) (set_o : s → a → s)
    (get_i : a → u) (set_i : a → u → a)
    [ho : LawfulLens get_o set_o] [hi : LawfulLens get_i set_i] :
    ∀ (s : s) (v v' : u),
      composed_set get_o set_o set_i (composed_set get_o set_o set_i s v) v' =
      composed_set get_o set_o set_i s v' := by
  intro s v v'
  unfold composed_set
  -- Goal: set_o (set_o s (set_i (get_o s) v)) (set_i (get_o (set_o s (set_i (get_o s) v))) v') = set_o s (set_i (get_o s) v')
  -- Apply ho.getput to simplify get_o (set_o s (set_i (get_o s) v))
  rw [ho.getput]
  -- Now goal: set_o (set_o s (set_i (get_o s) v)) (set_i (get_i (get_o s)) v') = set_o s (set_i (get_o s) v')
  -- Apply hi.putput to simplify set_i (get_i (get_o s))
  rw [hi.putput]
  -- Now goal: set_o (set_o s (set_i (get_o s) v)) (set_i (get_o s) v') = set_o s (set_i (get_o s) v')
  -- Apply ho.putput
  exact ho.putput s (set_i (get_o s) v) (set_i (get_o s) v')

/--
**Composition is Lawful**: If two lenses are lawful, their composition forms a lawful lens.
-/
instance composedLens_isLawful {s a u : Type}
    (get_o : s → a) (set_o : s → a → s)
    (get_i : a → u) (set_i : a → u → a)
    [ho : LawfulLens get_o set_o] [hi : LawfulLens get_i set_i] :
    LawfulLens (composed_get get_o get_i) (composed_set get_o set_o set_i) where
  getput := composeLens_preserves_getput get_o set_o get_i set_i
  putget := composeLens_preserves_putget get_o set_o get_i set_i
  putput := composeLens_preserves_putput get_o set_o get_i set_i


/-! ## Examples -/

/--
Example: The first projection lens `_1` is lawful.
-/
instance : LawfulLens (fun (p : α × β) => p.1) (fun p a => (a, p.2)) where
  getput := by intro _ _; rfl
  putget := by intro ⟨a, b⟩; rfl
  putput := by intro _ _ _; rfl

/--
Example: The second projection lens `_2` is lawful.
-/
instance : LawfulLens (fun (p : α × β) => p.2) (fun p b => (p.1, b)) where
  getput := by intro _ _; rfl
  putget := by intro ⟨a, b⟩; rfl
  putput := by intro _ _ _; rfl

end Collimator.Theorems
