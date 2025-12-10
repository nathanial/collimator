import Collimator.Optics

namespace Collimator.Instances.Sum

open Collimator


/-- Prism focusing the left branch of a sum (polymorphic version). -/
@[inline] def left {α β γ : Type} :
    Prism (Sum α β) (Sum γ β) α γ :=
  prism (s := Sum α β) (t := Sum γ β) (a := α) (b := γ)
    (build := Sum.inl)
    (split :=
      fun
      | Sum.inl a => Sum.inr a
      | Sum.inr b => Sum.inl (Sum.inr b))

/-- Monomorphic version of left prism for easier use in compositions.

Usage in compositions:
```lean
-- Clean syntax with monomorphic version
left' String Employee

-- vs polymorphic version requiring all type parameters
left (α := String) (β := Employee) (γ := String)
```
-/
@[inline] def left' (α β : Type) : Prism' (Sum α β) α := left

/-- Prism focusing the right branch of a sum (polymorphic version). -/
@[inline] def right {α β γ : Type} :
    Prism (Sum α β) (Sum α γ) β γ :=
  prism (s := Sum α β) (t := Sum α γ) (a := β) (b := γ)
    (build := Sum.inr)
    (split :=
      fun
      | Sum.inr b => Sum.inr b
      | Sum.inl a => Sum.inl (Sum.inl a))

/-- Monomorphic version of right prism for easier use in compositions.

Usage in compositions:
```lean
-- Clean syntax with monomorphic version
right' String Employee

-- vs polymorphic version requiring all type parameters
right (α := String) (β := Employee) (γ := Employee)
```
-/
@[inline] def right' (α β : Type) : Prism' (Sum α β) β := right

end Collimator.Instances.Sum
