import Collimator.Core
import Collimator.Optics
import Collimator.Concrete.Forget
import Collimator.Concrete.Tagged
import Collimator.Combinators

/-!
# Isomorphism Laws

This module formalizes and proves the two fundamental isomorphism laws for profunctor optics:
1. **Back-Forward** (Round-trip): Applying back after forward gives the identity
2. **Forward-Back** (Inverse): Applying forward after back gives the identity

## References
- Profunctor Optics: Modular Data Accessors (Pickering, Gibbons, Wu)
- ProfunctorOpticsDesign.md Phase 5
-/

namespace Collimator.Theorems

open Collimator
open Collimator.Core
open Collimator.Concrete


/-! ## Accessor Functions -/

/--
Apply an isomorphism in the forward direction.
Uses the Forget profunctor which only applies the pre-processing function.
-/
def isoForward {s a : Type} (i : Iso' s a) (x : s) : a :=
  let forget : Forget a a a := fun y => y
  let result := i (P := fun α β => Forget a α β) forget
  result x

/--
Apply an isomorphism in the backward direction.
Uses the Tagged profunctor which only applies the post-processing function.
-/
def isoBackward {s a : Type} (i : Iso' s a) (x : a) : s :=
  i (P := fun α β => Tagged α β) x

/-! ## Lawful Isomorphism Class -/

/--
A lawful isomorphism requires the forward and backward functions to be inverses.

For an isomorphism to be lawful, the two functions must satisfy:
1. Going forward then backward returns the original value (back-forward law)
2. Going backward then forward returns the original value (forward-back law)
-/
class LawfulIso {s : Type} {a : Type}
    (forward : s → a) (back : a → s) where
  /-- Applying back after forward gives the identity (round-trip law). -/
  back_forward : ∀ (x : s), back (forward x) = x
  /-- Applying forward after back gives the identity (inverse law). -/
  forward_back : ∀ (x : a), forward (back x) = x

/-! ## Helper Lemmas -/

/--
Unfolding lemma: `isoForward` applied to an iso constructed from forward/back.
-/
theorem isoForward_iso_eq {s a : Type} (forward : s → a) (back : a → s) (x : s) :
    isoForward (iso forward back) x = forward x := by
  unfold isoForward iso
  rfl

/--
Unfolding lemma: `isoBackward` applied to an iso constructed from forward/back.
-/
theorem isoBackward_iso_eq {s a : Type} (forward : s → a) (back : a → s) (x : a) :
    isoBackward (iso forward back) x = back x := by
  unfold isoBackward iso
  rfl

/-! ## Main Isomorphism Laws -/

/--
**Back-Forward Law**: Applying the backward function after the forward function
returns the original value.

If `i = iso forward back` and the underlying functions satisfy `back ∘ forward = id`,
then `isoBackward i ∘ isoForward i = id`.
-/
theorem iso_back_forward {s a : Type} (forward : s → a) (back : a → s)
    (h : ∀ (x : s), back (forward x) = x) :
    ∀ (x : s), isoBackward (iso forward back) (isoForward (iso forward back) x) = x := by
  intro x
  rw [isoForward_iso_eq, isoBackward_iso_eq]
  exact h x

/--
**Forward-Back Law**: Applying the forward function after the backward function
returns the original value.

If `i = iso forward back` and the underlying functions satisfy `forward ∘ back = id`,
then `isoForward i ∘ isoBackward i = id`.
-/
theorem iso_forward_back {s a : Type} (forward : s → a) (back : a → s)
    (h : ∀ (x : a), forward (back x) = x) :
    ∀ (x : a), isoForward (iso forward back) (isoBackward (iso forward back) x) = x := by
  intro x
  rw [isoForward_iso_eq, isoBackward_iso_eq]
  exact h x

/-! ## Bundled Lawful Iso Theorems -/

/--
If the underlying forward/back functions form a lawful isomorphism, then both iso laws hold
for the profunctor iso constructed from them.
-/
theorem lawful_iso_satisfies_laws {s a : Type} (forward : s → a) (back : a → s)
    [h : LawfulIso forward back] :
    (∀ (x : s), isoBackward (iso forward back) (isoForward (iso forward back) x) = x) ∧
    (∀ (x : a), isoForward (iso forward back) (isoBackward (iso forward back) x) = x) := by
  constructor
  · exact iso_back_forward forward back h.back_forward
  · exact iso_forward_back forward back h.forward_back

/-! ## Isomorphism Composition Laws -/

open Collimator.Combinators

/--
Helper: Extract forward function from composed isos.
-/
private def composed_forward {s u a : Type}
    (forward_outer : s → u) (forward_inner : u → a) : s → a :=
  forward_inner ∘ forward_outer

/--
Helper: Extract backward function from composed isos.
-/
private def composed_back {s u a : Type}
    (back_outer : u → s) (back_inner : a → u) : a → s :=
  back_outer ∘ back_inner

/--
**Composition Preserves Back-Forward**: If two isos are lawful, their composition
preserves the back-forward law.
-/
theorem composeIso_preserves_back_forward {s u a : Type}
    (forward_o : s → u) (back_o : u → s)
    (forward_i : u → a) (back_i : a → u)
    [ho : LawfulIso forward_o back_o] [hi : LawfulIso forward_i back_i] :
    ∀ (x : s),
      composed_back back_o back_i (composed_forward forward_o forward_i x) = x := by
  intro x
  unfold composed_back composed_forward
  simp only [Function.comp_apply]
  rw [hi.back_forward, ho.back_forward]

/--
**Composition Preserves Forward-Back**: If two isos are lawful, their composition
preserves the forward-back law.
-/
theorem composeIso_preserves_forward_back {s u a : Type}
    (forward_o : s → u) (back_o : u → s)
    (forward_i : u → a) (back_i : a → u)
    [ho : LawfulIso forward_o back_o] [hi : LawfulIso forward_i back_i] :
    ∀ (x : a),
      composed_forward forward_o forward_i (composed_back back_o back_i x) = x := by
  intro x
  unfold composed_back composed_forward
  simp only [Function.comp_apply]
  rw [ho.forward_back, hi.forward_back]

/--
**Composition is Lawful**: If two isos are lawful, their composition forms a lawful iso.
-/
instance composedIso_isLawful {s u a : Type}
    (forward_o : s → u) (back_o : u → s)
    (forward_i : u → a) (back_i : a → u)
    [ho : LawfulIso forward_o back_o] [hi : LawfulIso forward_i back_i] :
    LawfulIso (composed_forward forward_o forward_i) (composed_back back_o back_i) where
  back_forward := composeIso_preserves_back_forward forward_o back_o forward_i back_i
  forward_back := composeIso_preserves_forward_back forward_o back_o forward_i back_i

/-! ## Examples -/

/--
Example: Boolean negation is a lawful isomorphism with itself.
-/
instance : LawfulIso (not : Bool → Bool) (not : Bool → Bool) where
  back_forward := by intro x; cases x <;> rfl
  forward_back := by intro x; cases x <;> rfl

/--
Example: Tuple swap is a lawful isomorphism.
-/
instance {α β : Type} : LawfulIso
    (fun (p : α × β) => (p.2, p.1))
    (fun (p : β × α) => (p.2, p.1)) where
  back_forward := by intro ⟨a, b⟩; rfl
  forward_back := by intro ⟨b, a⟩; rfl

/--
Example: Negation for integers is a lawful isomorphism with itself.
-/
instance : LawfulIso (fun x : Int => -x) (fun x : Int => -x) where
  back_forward := by intro x; omega
  forward_back := by intro x; omega

/--
Example: The identity function is a lawful isomorphism with itself.
-/
instance {α : Type} : LawfulIso (fun x : α => x) (fun x : α => x) where
  back_forward := by intro x; rfl
  forward_back := by intro x; rfl

end Collimator.Theorems
