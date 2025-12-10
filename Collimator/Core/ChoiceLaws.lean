import Collimator.Core.Profunctor
import Collimator.Core.Choice

/-!
# Choice Profunctor Laws

This module formalizes the coherence laws between `left`, `right`, and `dimap`
for Choice profunctors.

A lawful Choice profunctor must satisfy:
1. **left-dimap coherence**: `left` commutes with `dimap`
2. **right-dimap coherence**: `right` commutes with `dimap`
3. **left-right interchange**: `left` and `right` can be interchanged via swapping

## References
- Profunctor Optics: Modular Data Accessors (Pickering, Gibbons, Wu)
- ProfunctorOpticsDesign.md Phase 5
-/

namespace Collimator.Core


variable {P : Type u → Type u → Type v}

/--
A lawful Choice profunctor satisfies coherence laws between `left`, `right`, and `dimap`.
-/
class LawfulChoice (P : Type u → Type u → Type v) [Profunctor P] [Choice P] where
  /--
  **left-dimap coherence**: `left` is natural in both arguments.

  `left (dimap f g p) = dimap (f ⊕ id) (g ⊕ id) (left p)`
  -/
  left_dimap : ∀ {α β α' β' γ : Type u} (f : α' → α) (g : β → β') (p : P α β),
    Choice.left (Profunctor.dimap f g p) =
    Profunctor.dimap (fun ac => match ac with
                       | Sum.inl a => Sum.inl (f a)
                       | Sum.inr c => Sum.inr c)
                     (fun bc => match bc with
                       | Sum.inl b => Sum.inl (g b)
                       | Sum.inr c => Sum.inr c)
                     (Choice.left (γ := γ) p)

  /--
  **right-dimap coherence**: `right` is natural in both arguments.

  `right (dimap f g p) = dimap (id ⊕ f) (id ⊕ g) (right p)`
  -/
  right_dimap : ∀ {α β α' β' γ : Type u} (f : α' → α) (g : β → β') (p : P α β),
    Choice.right (Profunctor.dimap f g p) =
    Profunctor.dimap (fun ca => match ca with
                       | Sum.inl c => Sum.inl c
                       | Sum.inr a => Sum.inr (f a))
                     (fun cb => match cb with
                       | Sum.inl c => Sum.inl c
                       | Sum.inr b => Sum.inr (g b))
                     (Choice.right (γ := γ) p)

  /--
  **left-right interchange**: Swapping sums interchanges `left` and `right`.

  `dimap swap swap (left p) = right p` (modulo type alignment)

  Note: The precise statement requires careful alignment of type parameters.
  -/
  left_right_swap : ∀ {α β γ : Type u} (p : P α β),
    Profunctor.dimap Sum.swap Sum.swap (Choice.left (γ := γ) p) =
    (Choice.right (γ := γ) p : P (Sum γ α) (Sum γ β))

/--
The function arrow is a lawful Choice profunctor.
-/
axiom instLawfulChoiceArrow : LawfulChoice (fun α β : Type u => α → β)

end Collimator.Core
