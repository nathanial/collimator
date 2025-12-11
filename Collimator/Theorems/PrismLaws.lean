import Collimator.Core
import Collimator.Optics
import Collimator.Concrete.Forget
import Collimator.Concrete.Tagged
import Collimator.Combinators

/-!
# Prism Laws

This module formalizes and proves the two fundamental prism laws for profunctor optics:
1. **Preview-Review**: Previewing after reviewing gives you back what you reviewed
2. **Review-Preview** (Right Inverse): If preview succeeds, reviewing the result reconstructs the original

## References
- Profunctor Optics: Modular Data Accessors (Pickering, Gibbons, Wu)
- ProfunctorOpticsDesign.md Phase 5
-/

namespace Collimator.Theorems

open Collimator
open Collimator.Core
open Collimator.Concrete


/--
A lawful prism requires the underlying build and split functions to satisfy two laws.
-/
class LawfulPrism {s : Type} {a : Type}
    (build : a → s) (split : s → Sum s a) where
  /-- Previewing after reviewing returns the value that was reviewed. -/
  preview_review : ∀ (b : a), split (build b) = Sum.inr b
  /-- If preview succeeds, reviewing the result reconstructs the original value. -/
  review_preview : ∀ (s : s) (a : a), split s = Sum.inr a → build a = s

/-! ## Helper Lemmas -/

private theorem default_option_none {α : Type} : (default : Option α) = none := rfl

/--
Unfolding lemma: `preview` applied to a prism constructed from build/split.
-/
theorem preview_prism_eq {s a : Type} (build : a → s) (split : s → Sum s a) (x : s) :
    preview' (prism build split) x =
      match split x with
      | Sum.inl _ => none
      | Sum.inr a => some a := by
  unfold preview' prism
  simp only [Profunctor.dimap, Choice.right]
  split <;> (next heq => simp only [heq, default_option_none])

/--
Unfolding lemma: `review` applied to a prism constructed from build/split.
-/
theorem review_prism_eq {s a : Type} (build : a → s) (split : s → Sum s a) (b : a) :
    review' (prism build split) b = build b := by
  unfold review' prism
  rfl

/-! ## Main Prism Laws -/

/--
**Preview-Review Law**: Previewing after reviewing returns the value that was reviewed.

If `p = prism build split` and the underlying functions satisfy
`split (build b) = Sum.inr b`, then `preview p (review p b) = some b`.
-/
theorem prism_preview_review {s a : Type} (build : a → s) (split : s → Sum s a)
    (h : ∀ (b : a), split (build b) = Sum.inr b) :
    ∀ (b : a), preview' (prism build split) (review' (prism build split) b) = some b := by
  intro b
  rw [review_prism_eq, preview_prism_eq]
  simp [h b]

/--
**Review-Preview Law** (Right Inverse): If preview succeeds, reviewing the result
reconstructs the original value.

If `p = prism build split` and the underlying functions satisfy
`split s = Sum.inr a → build a = s`, then
`preview p s = some a → review p a = s`.
-/
theorem prism_review_preview {s a : Type} (build : a → s) (split : s → Sum s a)
    (h : ∀ (s : s) (a : a), split s = Sum.inr a → build a = s) :
    ∀ (s : s) (a : a), preview' (prism build split) s = some a → review' (prism build split) a = s := by
  intro s a hprev
  rw [preview_prism_eq] at hprev
  split at hprev
  · contradiction
  · next a' hcase =>
    simp at hprev
    subst hprev
    rw [review_prism_eq]
    exact h s a' hcase

/-! ## Bundled Lawful Prism Theorems -/

/--
If the underlying build/split functions form a lawful prism, then both prism laws hold
for the profunctor prism constructed from them.
-/
theorem lawful_prism_satisfies_laws {s a : Type} (build : a → s) (split : s → Sum s a)
    [h : LawfulPrism build split] :
    (∀ (b : a), preview' (prism build split) (review' (prism build split) b) = some b) ∧
    (∀ (s : s) (a : a), preview' (prism build split) s = some a → review' (prism build split) a = s) := by
  constructor
  · exact prism_preview_review build split h.preview_review
  · exact prism_review_preview build split h.review_preview

/-! ## Prism Composition Laws -/

open Collimator.Combinators

/--
Helper: Extract builder from composed prisms.
-/
private def composed_build {s a u : Type}
    (build_outer : a → s) (build_inner : u → a) : u → s :=
  build_outer ∘ build_inner

/--
Helper: Extract splitter from composed prisms.
-/
private def composed_split {s a u : Type}
    (split_outer : s → Sum s a) (split_inner : a → Sum a u) : s → Sum s u :=
  fun s => match split_outer s with
    | Sum.inl s' => Sum.inl s'
    | Sum.inr a => match split_inner a with
      | Sum.inl _ => Sum.inl s
      | Sum.inr u => Sum.inr u

/--
**Composition Preserves Preview-Review**: If two prisms are lawful, their composition
preserves the preview-review law.
-/
theorem composePrism_preserves_preview_review {s a u : Type}
    (build_o : a → s) (split_o : s → Sum s a)
    (build_i : u → a) (split_i : a → Sum a u)
    [ho : LawfulPrism build_o split_o] [hi : LawfulPrism build_i split_i] :
    ∀ (b : u),
      composed_split split_o split_i (composed_build build_o build_i b) = Sum.inr b := by
  intro b
  unfold composed_split composed_build
  simp only [Function.comp_apply]
  rw [ho.preview_review]
  simp only []
  rw [hi.preview_review]

/--
**Composition Preserves Review-Preview**: If two prisms are lawful, their composition
preserves the review-preview law.
-/
theorem composePrism_preserves_review_preview {s a u : Type}
    (build_o : a → s) (split_o : s → Sum s a)
    (build_i : u → a) (split_i : a → Sum a u)
    [ho : LawfulPrism build_o split_o] [hi : LawfulPrism build_i split_i] :
    ∀ (s : s) (u : u),
      composed_split split_o split_i s = Sum.inr u →
      composed_build build_o build_i u = s := by
  intro s u hsplit
  unfold composed_split at hsplit
  split at hsplit
  · next _ => contradiction
  · next a ha =>
    split at hsplit
    · next _ => contradiction
    · next u' hu =>
      simp at hsplit
      subst hsplit
      unfold composed_build
      simp
      have h1 := hi.review_preview a u' hu
      have h2 := ho.review_preview s a ha
      rw [← h1] at h2
      exact h2

/--
**Composition is Lawful**: If two prisms are lawful, their composition forms a lawful prism.
-/
instance composedPrism_isLawful {s a u : Type}
    (build_o : a → s) (split_o : s → Sum s a)
    (build_i : u → a) (split_i : a → Sum a u)
    [ho : LawfulPrism build_o split_o] [hi : LawfulPrism build_i split_i] :
    LawfulPrism (composed_build build_o build_i) (composed_split split_o split_i) where
  preview_review := composePrism_preserves_preview_review build_o split_o build_i split_i
  review_preview := composePrism_preserves_review_preview build_o split_o build_i split_i

/-! ## Examples -/

/--
Example: The Some constructor for Option is a lawful prism.
-/
instance : LawfulPrism (some : α → Option α)
    (fun s => match s with | some a => Sum.inr a | none => Sum.inl none) where
  preview_review := by intro _; rfl
  review_preview := by intro s a h; cases s <;> simp at h; simp [h]

end Collimator.Theorems
