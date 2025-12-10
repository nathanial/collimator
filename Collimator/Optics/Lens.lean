import Collimator.Core.Profunctor
import Collimator.Core.Strong
import Collimator.Optics.Types
import Collimator.Concrete.Forget
import Collimator.Concrete.FunArrow

namespace Collimator

open Collimator.Core
open Collimator.Concrete

universe u

/--
Construct a lens from getter and setter functions.
-/
def lens' {s : Type u} {t : Type u} {a : Type u} {b : Type u}
    (get : s → a) (set : s → b → t) : Lens s t a b :=
  fun {P} [Profunctor P] hStrong pab =>
    let _ : Strong P := hStrong
    let _ := (inferInstance : Profunctor P)
    let first := Strong.first (P := P) (γ := s) pab
    Profunctor.dimap (P := P)
      (fun s => (get s, s))
      (fun bs => set bs.2 bs.1)
      first

/-- View the focus of a lens. -/
def view' {s a : Type _} (l : Lens' s a) (x : s) : a :=
  let forget : Forget a a a := fun a => a
  let result := l.toLens (P := fun α β => Forget a α β) inferInstance forget
  result x

/-- Modify the focus of a lens. -/
def over' {s t a b : Type _}
    (l : Lens s t a b) (f : a → b) : s → t :=
  let arrow := FunArrow.mk (α := a) (β := b) f
  let result := l.toLens (P := fun α β => FunArrow α β) inferInstance arrow
  fun s => result s

/-- Set the focus of a lens to a constant value. -/
def set' {s t a b : Type _}
    (l : Lens s t a b) (v : b) : s → t :=
  over' l (fun _ => v)

/-- Lens focusing the first component of a pair. -/
def _1 {α β γ : Type _} :
    Lens (α × β) (γ × β) α γ :=
  lens' (fun p => p.1) (fun p b => (b, p.2))

/-- Lens focusing the second component of a pair. -/
def _2 {α β γ : Type _} :
    Lens (α × β) (α × γ) β γ :=
  lens' (fun p => p.2) (fun p b => (p.1, b))

/-- Lens that exposes a constant value without modifying the source. -/
def const {s a : Type _} (value : a) : Lens' s a :=
  lens' (fun _ => value) (fun s _ => s)

end Collimator
