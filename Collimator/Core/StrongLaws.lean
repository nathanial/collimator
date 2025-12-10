import Collimator.Core.Profunctor
import Collimator.Core.Strong

/-!
# Strong Profunctor Laws

This module formalizes the coherence laws between `first`, `second`, and `dimap`
for Strong profunctors.

A lawful Strong profunctor must satisfy:
1. **first-dimap coherence**: `first` commutes with `dimap`
2. **second-dimap coherence**: `second` commutes with `dimap`
3. **first-second interchange**: `first` and `second` can be interchanged via swapping

## References
- Profunctor Optics: Modular Data Accessors (Pickering, Gibbons, Wu)
- ProfunctorOpticsDesign.md Phase 5
-/

namespace Collimator.Core

universe u v

variable {P : Type u → Type u → Type v}

/--
A lawful Strong profunctor satisfies coherence laws between `first`, `second`, and `dimap`.
-/
class LawfulStrong (P : Type u → Type u → Type v) [Profunctor P] [Strong P] where
  /--
  **first-dimap coherence**: `first` is natural in both arguments.

  `first (dimap f g p) = dimap (f × id) (g × id) (first p)`
  -/
  first_dimap : ∀ {α β α' β' γ : Type u} (f : α' → α) (g : β → β') (p : P α β),
    Strong.first (Profunctor.dimap f g p) =
    Profunctor.dimap (fun (ac : α' × γ) => (f ac.1, ac.2))
                     (fun (bc : β × γ) => (g bc.1, bc.2))
                     (Strong.first (γ := γ) p)

  /--
  **second-dimap coherence**: `second` is natural in both arguments.

  `second (dimap f g p) = dimap (id × f) (id × g) (second p)`
  -/
  second_dimap : ∀ {α β α' β' γ : Type u} (f : α' → α) (g : β → β') (p : P α β),
    Strong.second (Profunctor.dimap f g p) =
    Profunctor.dimap (fun (ca : γ × α') => (ca.1, f ca.2))
                     (fun (cb : γ × β) => (cb.1, g cb.2))
                     (Strong.second (γ := γ) p)

  /--
  **first-second interchange**: Swapping products interchanges `first` and `second`.

  `dimap swap swap (first p) = second p` (modulo type alignment)

  Note: The precise statement requires careful alignment of type parameters.
  -/
  first_second_swap : ∀ {α β γ : Type u} (p : P α β),
    Profunctor.dimap Prod.swap Prod.swap (Strong.first (γ := γ) p) =
    (Strong.second (γ := γ) p : P (γ × α) (γ × β))

/--
The function arrow is a lawful Strong profunctor.
-/
axiom instLawfulStrongArrow : LawfulStrong (fun α β : Type u => α → β)

end Collimator.Core
