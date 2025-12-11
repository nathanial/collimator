import Collimator.Core
import Collimator.Optics
import Collimator.Concrete.Forget
import Collimator.Concrete.FunArrow
import Collimator.Combinators

/-!
# Affine Traversal Laws

This module formalizes the laws for affine traversals - optics that focus on
at most one element (0 or 1 focus).

An affine traversal combines aspects of both lenses (at most one focus) and
prisms (may fail to match). When the focus exists, it behaves like a lens;
when it doesn't exist, operations leave the structure unchanged.

## The Three Affine Traversal Laws

1. **SetPreview**: Setting then previewing yields the set value (when focus exists)
2. **PreviewSet**: Setting to the current preview value is identity
3. **SetSet**: Setting twice uses the last value

## References
- Profunctor Optics: Modular Data Accessors (Pickering, Gibbons, Wu)
- ProfunctorOpticsDesign.md Phase 5
-/

namespace Collimator.Theorems

open Collimator
open Collimator.Core
open Collimator.Concrete


/-! ## Lawful Affine Traversal Class -/

/--
A lawful affine traversal requires the underlying preview and set functions to
satisfy three laws.

An affine traversal focuses on **at most one** element (may have 0 or 1 focus).
- When derived from a lens: preview always succeeds (exactly 1 focus)
- When derived from a prism: preview may fail (0 or 1 focus)
-/
class LawfulAffineTraversal {s : Type} {a : Type}
    (preview : s → Option a) (set : s → a → s) where
  /-- Setting then previewing gives Some of the set value (when focus exists). -/
  set_preview : ∀ (s : s) (v : a),
    preview s ≠ none → preview (set s v) = some v
  /-- If preview finds value 'a', then setting to 'a' doesn't change anything. -/
  preview_set : ∀ (s : s) (a : a),
    preview s = some a → set s a = s
  /-- Setting twice uses the last value. -/
  set_set : ∀ (s : s) (v v' : a),
    set (set s v) v' = set s v'

/-! ## Helper Lemmas -/

/--
Unfolding lemma: `AffineTraversalOps.preview` applied to an affine traversal
constructed from preview/set functions.
-/
theorem affine_preview_eq {s a : Type}
    (preview : s → Option a) (set : s → a → s)
    (x : s) :
    ∃ (aff : AffineTraversal' s a),
      AffineTraversalOps.preview' aff x = preview x := by
  -- Convert preview function to a sum type for profunctor encoding
  let split : s → Sum s a := fun s =>
    match preview s with
    | none => Sum.inl s
    | some a => Sum.inr a

  -- Construct the affine traversal using profunctor optics encoding
  let aff : AffineTraversal' s a :=
    fun {P} [Profunctor P] (hStrong : Strong P) (hChoice : Choice P) paa =>
      let _ : Strong P := hStrong
      let _ : Choice P := hChoice
      -- Apply Choice.right to handle the Sum
      let right := Choice.right (P := P) (γ := s) paa
      -- Apply Strong.first to thread through the original value
      let paired := Strong.first (P := P) (γ := s) right
      -- Use dimap to shape input and output
      Profunctor.dimap (P := P)
        (fun s => (split s, s))
        (fun result_pair : Sum s a × s =>
          match result_pair.1 with
          | Sum.inl s' => s'
          | Sum.inr a' => set result_pair.2 a')
        paired

  -- Provide the witness
  refine ⟨aff, ?_⟩

  -- Prove the equation: AffineTraversalOps.preview aff x = preview x
  -- Unfold the definition of preview
  unfold AffineTraversalOps.preview' aff
  simp only []

  -- Unfold the profunctor operations
  unfold Profunctor.dimap Strong.first Choice.right
  unfold instStrongForget instChoiceForget instProfunctorForget
  simp only []

  -- Case analyze on preview x to show both branches are equal
  cases hprev : preview x with
  | none =>
    unfold split
    simp only [hprev]
    -- Goal: default = none (for Option a, default is none)
    rfl
  | some a =>
    unfold split
    simp only [hprev]

/--
Unfolding lemma: `AffineTraversalOps.set` applied to an affine traversal
constructed from preview/set functions.

Note: This only holds when there is a focus (preview x ≠ none). When there's
no focus, an affine traversal correctly returns the structure unchanged.
-/
theorem affine_set_eq {s a : Type}
    (preview : s → Option a) (set : s → a → s)
    (v : a) (x : s)
    (h_focus : preview x ≠ none) :
    ∃ (aff : AffineTraversal' s a),
      AffineTraversalOps.set aff v x = set x v := by
  -- Reuse the same construction from affine_preview_eq
  let split : s → Sum s a := fun s =>
    match preview s with
    | none => Sum.inl s
    | some a => Sum.inr a

  let aff : AffineTraversal' s a :=
    fun {P} [Profunctor P] (hStrong : Strong P) (hChoice : Choice P) paa =>
      let _ : Strong P := hStrong
      let _ : Choice P := hChoice
      let right := Choice.right (P := P) (γ := s) paa
      let paired := Strong.first (P := P) (γ := s) right
      Profunctor.dimap (P := P)
        (fun s => (split s, s))
        (fun result_pair : Sum s a × s =>
          match result_pair.1 with
          | Sum.inl s' => s'
          | Sum.inr a' => set result_pair.2 a')
        paired

  refine ⟨aff, ?_⟩

  -- Prove the equation: AffineTraversalOps.set aff v x = set x v
  -- Unfold set and over
  unfold AffineTraversalOps.set AffineTraversalOps.over aff
  simp only []

  -- Unfold the profunctor operations for FunArrow
  unfold Profunctor.dimap Strong.first Choice.right
  unfold instProfunctorFunArrow instStrongFunArrow instChoiceFunArrow
  simp only []

  -- Since h_focus : preview x ≠ none, we know preview x = some a for some a
  cases hprev : preview x with
  | none =>
    -- This case contradicts h_focus
    contradiction
  | some a =>
    -- In this case, split x = Sum.inr a
    unfold split
    simp only [hprev]

/-! ## Main Affine Traversal Laws -/

/--
**SetPreview Law**: Previewing an affine traversal after setting it returns
the value that was set (when the focus exists).

This theorem simply extracts the `set_preview` field from the LawfulAffineTraversal instance.
-/
theorem affine_set_preview {s a : Type}
    (preview : s → Option a) (set : s → a → s)
    [h : LawfulAffineTraversal preview set] :
    ∀ (s : s) (v : a),
      preview s ≠ none → preview (set s v) = some v :=
  h.set_preview

/--
**PreviewSet Law**: Setting an affine traversal to its current preview value
doesn't change the structure.

This theorem simply extracts the `preview_set` field from the LawfulAffineTraversal instance.
-/
theorem affine_preview_set {s a : Type}
    (preview : s → Option a) (set : s → a → s)
    [h : LawfulAffineTraversal preview set] :
    ∀ (s : s) (a : a),
      preview s = some a → set s a = s :=
  h.preview_set

/--
**SetSet Law**: Setting an affine traversal twice is the same as setting
once with the last value.

This theorem simply extracts the `set_set` field from the LawfulAffineTraversal instance.
-/
theorem affine_set_set {s a : Type}
    (preview : s → Option a) (set : s → a → s)
    [h : LawfulAffineTraversal preview set] :
    ∀ (s : s) (v v' : a),
      set (set s v) v' = set s v' :=
  h.set_set

/-! ## Bundled Lawful Affine Theorems -/

/--
If the underlying preview/set functions form a lawful affine traversal,
then all three affine laws hold.

This theorem bundles the three laws together by extracting all three fields
from the LawfulAffineTraversal instance.
-/
theorem lawful_affine_satisfies_laws {s a : Type}
    (preview : s → Option a) (set : s → a → s)
    [h : LawfulAffineTraversal preview set] :
    (∀ (s : s) (v : a), preview s ≠ none → preview (set s v) = some v) ∧
    (∀ (s : s) (a : a), preview s = some a → set s a = s) ∧
    (∀ (s : s) (v v' : a), set (set s v) v' = set s v') :=
  ⟨h.set_preview, h.preview_set, h.set_set⟩

/-! ## Affine Traversal Composition Laws -/

open Collimator.Combinators

/--
Helper: Extract preview function from composed affine traversals.
Composes two preview functions: first applies outer, then inner if outer succeeds.
-/
private def composed_affine_preview {s u a : Type}
    (preview_outer : s → Option u)
    (preview_inner : u → Option a) :
    s → Option a :=
  fun s =>
    match preview_outer s with
    | none => none
    | some u => preview_inner u

/--
Helper: Extract set function from composed affine traversals.
If outer preview fails, returns unchanged structure.
If outer preview succeeds, applies inner set then outer set.
-/
private def composed_affine_set {s u a : Type}
    (preview_outer : s → Option u) (set_outer : s → u → s)
    (set_inner : u → a → u) :
    s → a → s :=
  fun s a =>
    match preview_outer s with
    | none => s
    | some u => set_outer s (set_inner u a)

/--
**Composition Preserves SetPreview**: If two affine traversals are lawful,
their composition preserves the SetPreview law.

The proof works by chaining the SetPreview laws of both the outer and inner
affine traversals. When the composition has a focus, both levels must have
a focus, allowing us to apply both laws sequentially.
-/
theorem composeAffine_preserves_set_preview {s u a : Type}
    (preview_o : s → Option u) (set_o : s → u → s)
    (preview_i : u → Option a) (set_i : u → a → u)
    [ho : LawfulAffineTraversal preview_o set_o]
    [hi : LawfulAffineTraversal preview_i set_i] :
    ∀ (s : s) (v : a),
      composed_affine_preview preview_o preview_i s ≠ none →
      composed_affine_preview preview_o preview_i
        (composed_affine_set preview_o set_o set_i s v) = some v := by
  intro s v hfocus

  -- Unfold composed_affine_preview in the assumption to extract conditions
  unfold composed_affine_preview at hfocus

  -- Case analyze on preview_o s
  cases houter : preview_o s with
  | none =>
    -- If preview_o s = none, then composed preview is none, contradicting hfocus
    simp [houter] at hfocus
  | some u =>
    -- If preview_o s = some u, then we need preview_i u ≠ none
    simp [houter] at hfocus

    -- Now unfold the goal
    unfold composed_affine_preview composed_affine_set
    simp [houter]

    -- Apply outer's SetPreview law: preview_o (set_o s (set_i u v)) = some (set_i u v)
    have outer_law := ho.set_preview s (set_i u v)
    simp [houter] at outer_law
    rw [outer_law]

    -- Apply inner's SetPreview law: preview_i (set_i u v) = some v
    have inner_law := hi.set_preview u v hfocus
    exact inner_law

/--
**Composition Preserves PreviewSet**: If two affine traversals are lawful,
their composition preserves the PreviewSet law.

The proof works by applying both PreviewSet laws in sequence: first the inner
law to show that setting the inner value doesn't change it, then the outer law
to show that setting to the unchanged value doesn't change the structure.
-/
theorem composeAffine_preserves_preview_set {s u a : Type}
    (preview_o : s → Option u) (set_o : s → u → s)
    (preview_i : u → Option a) (set_i : u → a → u)
    [ho : LawfulAffineTraversal preview_o set_o]
    [hi : LawfulAffineTraversal preview_i set_i] :
    ∀ (s : s) (a : a),
      composed_affine_preview preview_o preview_i s = some a →
      composed_affine_set preview_o set_o set_i s a = s := by
  intro s a hprev

  -- Unfold composed_affine_preview to extract both conditions
  unfold composed_affine_preview at hprev

  -- Case analyze on preview_o s
  cases houter : preview_o s with
  | none =>
    -- If preview_o s = none, then composed preview is none, contradiction
    simp [houter] at hprev
  | some u =>
    -- If preview_o s = some u, then hprev tells us preview_i u = some a
    simp [houter] at hprev

    -- Unfold composed_affine_set
    unfold composed_affine_set
    simp [houter]

    -- Goal: set_o s (set_i u a) = s
    -- Apply inner's PreviewSet law: set_i u a = u
    have inner_law := hi.preview_set u a hprev
    rw [inner_law]

    -- Goal: set_o s u = s
    -- Apply outer's PreviewSet law
    have outer_law := ho.preview_set s u houter
    exact outer_law

/--
**Composition Preserves SetSet**: If two affine traversals are lawful,
their composition preserves the SetSet law.

The proof works by applying both SetSet laws: first the inner law to collapse
consecutive inner sets, then the outer law to collapse consecutive outer sets.
-/
theorem composeAffine_preserves_set_set {s u a : Type}
    (preview_o : s → Option u) (set_o : s → u → s)
    (preview_i : u → Option a) (set_i : u → a → u)
    [ho : LawfulAffineTraversal preview_o set_o]
    [hi : LawfulAffineTraversal preview_i set_i] :
    ∀ (s : s) (v v' : a),
      composed_affine_set preview_o set_o set_i
        (composed_affine_set preview_o set_o set_i s v) v' =
      composed_affine_set preview_o set_o set_i s v' := by
  intro s v v'

  -- Case analyze on preview_o s
  cases houter : preview_o s with
  | none =>
    -- If no outer focus, all three sets return s unchanged
    unfold composed_affine_set
    simp [houter]
  | some u =>
    -- If outer focus exists, unfold the nested sets
    unfold composed_affine_set
    simp [houter]

    -- LHS: The first set gives us set_o s (set_i u v)
    -- We need to know what preview_o (set_o s (set_i u v)) is
    -- By outer's SetPreview law, it's some (set_i u v)
    have outer_preview := ho.set_preview s (set_i u v)
    simp [houter] at outer_preview

    -- Now the second set becomes: set_o (set_o s (set_i u v)) (set_i (set_i u v) v')
    simp [outer_preview]

    -- Apply inner's SetSet law: set_i (set_i u v) v' = set_i u v'
    have inner_law := hi.set_set u v v'
    rw [inner_law]

    -- Apply outer's SetSet law: set_o (set_o s x) y = set_o s y
    have outer_law := ho.set_set s (set_i u v) (set_i u v')
    exact outer_law

/--
**Composition is Lawful**: If two affine traversals are lawful,
their composition forms a lawful affine traversal.

This is the capstone theorem that bundles all three composition preservation
theorems together, showing that lawfulness is preserved through composition.
-/
instance composedAffine_isLawful {s u a : Type}
    (preview_o : s → Option u) (set_o : s → u → s)
    (preview_i : u → Option a) (set_i : u → a → u)
    [ho : LawfulAffineTraversal preview_o set_o]
    [hi : LawfulAffineTraversal preview_i set_i] :
    LawfulAffineTraversal
      (composed_affine_preview preview_o preview_i)
      (composed_affine_set preview_o set_o set_i) where
  set_preview := composeAffine_preserves_set_preview preview_o set_o preview_i set_i
  preview_set := composeAffine_preserves_preview_set preview_o set_o preview_i set_i
  set_set := composeAffine_preserves_set_set preview_o set_o preview_i set_i

/-! ## Examples -/

/--
Example: Option is a lawful affine traversal (prism-derived).
The preview is identity (returns the Option itself), and set always wraps in Some.

This models Option as an affine traversal where:
- `none` represents no focus (affine traversal with 0 elements)
- `some a` represents a focus on `a` (affine traversal with 1 element)
-/
instance option_affine_is_lawful {α : Type} :
    LawfulAffineTraversal
      (fun (x : Option α) => x)
      (fun (_ : Option α) (a : α) => some a) where
  -- SetPreview: preview (set s v) = some v when s ≠ none
  set_preview := by
    intro s v _hsome
    -- set s v = some v, and preview (some v) = some v
    rfl

  -- PreviewSet: set s a = s when preview s = some a
  preview_set := by
    intro s a hprev
    -- Since preview is identity, hprev : s = some a
    -- Need to show: some a = s
    rw [← hprev]

  -- SetSet: set (set s v) v' = set s v'
  set_set := by
    intro s v v'
    -- set (set s v) v' = set (some v) v' = some v'
    -- set s v' = some v'
    rfl

end Collimator.Theorems
