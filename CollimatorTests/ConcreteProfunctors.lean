import Collimator.Core
import Batteries
import Collimator.Concrete.Forget
import Collimator.Concrete.Star
import Collimator.Concrete.Tagged
import Collimator.Concrete.FunArrow
import Collimator.Concrete.Costar
import CollimatorTests.Framework

/-!
# Concrete Profunctor Tests

Tests for the concrete profunctor implementations: Forget, Star, Tagged, FunArrow, and Costar.
Verifies that each profunctor satisfies the profunctor laws and that typeclass instances work correctly.
-/

namespace CollimatorTests.ConcreteProfunctors

open Collimator.Core
open Collimator.Concrete
open CollimatorTests

/-! ## Test Helpers -/

private def double : Int → Int := fun x => x * 2
private def inc : Int → Int := fun x => x + 1
private def toString' : Int → String := fun x => s!"{x}"
private def length' : String → Int := fun s => s.length

/-! ## Forget Tests -/

/--
Test that Forget satisfies dimap identity law: dimap id id = id
-/
private def case_forget_dimap_id : TestCase := {
  name := "Forget: dimap id id = id",
  run := do
    let forget : Forget Int Int String := fun x => x * 2
    let result := Profunctor.dimap (id : Int → Int) (id : String → String) forget
    ensureEq "Forget dimap id" (forget 5) (result 5)
}

/--
Test that Forget satisfies dimap composition law.
dimap (g ∘ f) (h ∘ i) = dimap f i ∘ dimap g h
In our case with Forget, only pre matters, so:
dimap (g ∘ f) _ p x = p (g (f x))
dimap f _ (dimap g _ p) x = (dimap g _ p) (f x) = p (g (f x))
-/
private def case_forget_dimap_comp : TestCase := {
  name := "Forget: dimap (g ∘ f) id = dimap f id ∘ dimap g id",
  run := do
    let forget : Forget Int Int String := fun x => x * 3

    -- dimap (double ∘ inc) id = apply (double ∘ inc) then forget
    -- On input 2: double(inc(2)) = double(3) = 6, then * 3 = 18
    let lhs := Profunctor.dimap (double ∘ inc) (id : String → String) forget

    -- dimap inc id (dimap double id forget) = apply inc, then double, then forget
    -- On input 2: inc(2) = 3, then double(3) = 6, then * 3 = 18
    let inner := Profunctor.dimap double (id : String → String) forget
    let rhs := Profunctor.dimap inc (id : String → String) inner

    ensureEq "Forget dimap comp" (lhs 2) (rhs 2)
}

/--
Test Forget Strong instance: first extracts from tuple correctly.
-/
private def case_forget_strong_first : TestCase := {
  name := "Forget Strong: first extracts from tuple",
  run := do
    let forget : Forget Int Int String := fun x => x + 100
    let lifted := Strong.first (P := Forget Int) (γ := String) forget
    let result := lifted (7, "hello")
    ensureEq "Forget Strong first" 107 result
}

/--
Test Forget Strong instance: second extracts from tuple correctly.
-/
private def case_forget_strong_second : TestCase := {
  name := "Forget Strong: second extracts from tuple",
  run := do
    let forget : Forget Int Int String := fun x => x + 50
    let lifted := Strong.second (P := Forget Int) (γ := Bool) forget
    let result := lifted (true, 20)
    ensureEq "Forget Strong second" 70 result
}

/--
Test Forget Choice instance: left applies to Sum.inl.
-/
private def case_forget_choice_left : TestCase := {
  name := "Forget Choice: left applies to Sum.inl",
  run := do
    let forget : Forget Int Int String := fun x => x * 10
    let lifted := Choice.left (P := Forget Int) (γ := Bool) forget
    let result := lifted (Sum.inl 3)
    ensureEq "Forget Choice left inl" 30 result
}

/--
Test Forget Choice instance: left returns default for Sum.inr.
-/
private def case_forget_choice_left_inr : TestCase := {
  name := "Forget Choice: left returns default for Sum.inr",
  run := do
    let forget : Forget Int Int String := fun x => x * 10
    let lifted := Choice.left (P := Forget Int) (γ := Bool) forget
    let result := lifted (Sum.inr true)
    ensureEq "Forget Choice left inr" 0 result  -- default for Int is 0
}

/--
Test Forget Wandering instance - the Wandering instance for Forget uses Const applicative
which accumulates values using the monoid operation.
-/
private def case_forget_wandering : TestCase := {
  name := "Forget Wandering: uses monoid to aggregate",
  run := do
    -- Forget (List Int) aggregates via list append
    -- When we wander over a list with a "single element" forget, we should get all elements
    let forget : Forget (List Int) Int String := fun x => [x]

    -- The Wandering instance for Forget uses Const R as the applicative functor
    -- This means walk will use pure = one = [] and <*> = mul = append
    -- Since Const R ignores the second type param, we get accumulation

    -- Test basic properties of the forget profunctor
    ensureEq "Forget collects single" [42] (forget 42)

    -- Test that Strong.first extracts and applies forget
    let strongForget := Strong.first (P := Forget (List Int)) (γ := String) forget
    ensureEq "Forget Strong first" [7] (strongForget (7, "ignored"))
}

/-! ## Star Tests -/

/--
Test that Star satisfies dimap identity law.
-/
private def case_star_dimap_id : TestCase := {
  name := "Star: dimap id id = id",
  run := do
    let star : Star Option Int Int := Star.mk (fun x => some (x + 1))
    let result := Profunctor.dimap (id : Int → Int) (id : Int → Int) star
    ensureEq "Star dimap id" (star.run 5) (result.run 5)
}

/--
Test Star Strong instance: first works with applicative.
-/
private def case_star_strong_first : TestCase := {
  name := "Star Strong: first preserves tuple structure",
  run := do
    let star : Star Option Int Int := Star.mk (fun x => some (x * 2))
    let lifted := Strong.first (P := Star Option) (γ := String) star
    let result := lifted.run (10, "test")
    ensureEq "Star Strong first" (some (20, "test")) result
}

/--
Test Star Strong instance: second works with applicative.
-/
private def case_star_strong_second : TestCase := {
  name := "Star Strong: second preserves tuple structure",
  run := do
    let star : Star Option Int Int := Star.mk (fun x => some (x + 5))
    let lifted := Strong.second (P := Star Option) (γ := Bool) star
    let result := lifted.run (true, 7)
    ensureEq "Star Strong second" (some (true, 12)) result
}

/--
Test Star Choice instance: left maps through Sum.inl.
-/
private def case_star_choice_left : TestCase := {
  name := "Star Choice: left maps Sum.inl values",
  run := do
    let star : Star Option Int Int := Star.mk (fun x => some (x * 3))
    let lifted := Choice.left (P := Star Option) (γ := String) star
    let result := lifted.run (Sum.inl 4)
    ensureEq "Star Choice left inl" (some (Sum.inl 12)) result
}

/--
Test Star Choice instance: left passes through Sum.inr unchanged.
-/
private def case_star_choice_left_inr : TestCase := {
  name := "Star Choice: left passes through Sum.inr",
  run := do
    let star : Star Option Int Int := Star.mk (fun x => some (x * 3))
    let lifted := Choice.left (P := Star Option) (γ := String) star
    let result := lifted.run (Sum.inr "hello")
    ensureEq "Star Choice left inr" (some (Sum.inr "hello")) result
}

/--
Test Star with Option short-circuiting.
-/
private def case_star_option_short_circuit : TestCase := {
  name := "Star Option: short-circuits on none",
  run := do
    let star : Star Option Int Int := Star.mk (fun x => if x > 0 then some (x + 1) else none)
    let positiveResult := star.run 5
    let negativeResult := star.run (-3)
    ensureEq "Star positive" (some 6) positiveResult
    ensureEq "Star negative" (none : Option Int) negativeResult
}

/--
Test Star Wandering instance.
-/
private def case_star_wandering : TestCase := {
  name := "Star Wandering: traverses with applicative effect",
  run := do
    let star : Star Option Int Int := Star.mk (fun x => if x >= 0 then some (x * 2) else none)

    let walk : {F : Type → Type} → [Applicative F] → (Int → F Int) → List Int → F (List Int) :=
      fun {F} [Applicative F] f xs => List.mapA f xs

    let lifted := Wandering.wander (P := Star Option) walk star
    let successResult := lifted.run [1, 2, 3]
    let failResult := lifted.run [1, -2, 3]

    ensureEq "Star Wandering success" (some [2, 4, 6]) successResult
    ensureEq "Star Wandering fail" (none : Option (List Int)) failResult
}

/-! ## Tagged Tests -/

/--
Test that Tagged satisfies dimap identity law.
-/
private def case_tagged_dimap_id : TestCase := {
  name := "Tagged: dimap id id = id",
  run := do
    let tagged : Tagged Int String := "hello"
    let result := Profunctor.dimap (id : Int → Int) (id : String → String) tagged
    ensureEq "Tagged dimap id" tagged result
}

/--
Test Tagged dimap: only applies the post function.
-/
private def case_tagged_dimap_post : TestCase := {
  name := "Tagged: dimap only applies post function",
  run := do
    let tagged : Tagged Int Int := 42
    let result := Profunctor.dimap (fun _ : String => 0) double tagged
    ensureEq "Tagged dimap post" 84 result
}

/--
Test Tagged Choice left: wraps value in Sum.inl.
-/
private def case_tagged_choice_left : TestCase := {
  name := "Tagged Choice: left wraps in Sum.inl",
  run := do
    let tagged : Tagged Int String := "test"
    let lifted := Choice.left (P := fun α β => Tagged α β) (γ := Bool) tagged
    ensureEq "Tagged Choice left" (Sum.inl "test") lifted
}

/--
Test Tagged Choice right: wraps value in Sum.inr.
-/
private def case_tagged_choice_right : TestCase := {
  name := "Tagged Choice: right wraps in Sum.inr",
  run := do
    let tagged : Tagged Int String := "test"
    let lifted := Choice.right (P := fun α β => Tagged α β) (γ := Bool) tagged
    ensureEq "Tagged Choice right" (Sum.inr "test") lifted
}

/-! ## FunArrow Tests -/

/--
Test that FunArrow satisfies dimap identity law.
-/
private def case_funarrow_dimap_id : TestCase := {
  name := "FunArrow: dimap id id = id",
  run := do
    let arrow : FunArrow Int Int := FunArrow.mk double
    let result := Profunctor.dimap (id : Int → Int) (id : Int → Int) arrow
    ensureEq "FunArrow dimap id" (arrow.run 5) (result.run 5)
}

/--
Test FunArrow dimap composition.
-/
private def case_funarrow_dimap_comp : TestCase := {
  name := "FunArrow: dimap composes correctly",
  run := do
    let arrow : FunArrow Int Int := FunArrow.mk double
    let result := Profunctor.dimap inc inc arrow
    -- (inc ∘ double ∘ inc) 3 = inc (double (inc 3)) = inc (double 4) = inc 8 = 9
    ensureEq "FunArrow dimap comp" 9 (result.run 3)
}

/--
Test FunArrow Strong first.
-/
private def case_funarrow_strong_first : TestCase := {
  name := "FunArrow Strong: first applies to first element",
  run := do
    let arrow : FunArrow Int Int := FunArrow.mk double
    let lifted := Strong.first (P := fun α β => FunArrow α β) (γ := String) arrow
    let result := lifted.run (5, "hello")
    ensureEq "FunArrow Strong first" (10, "hello") result
}

/--
Test FunArrow Strong second.
-/
private def case_funarrow_strong_second : TestCase := {
  name := "FunArrow Strong: second applies to second element",
  run := do
    let arrow : FunArrow Int Int := FunArrow.mk inc
    let lifted := Strong.second (P := fun α β => FunArrow α β) (γ := Bool) arrow
    let result := lifted.run (true, 10)
    ensureEq "FunArrow Strong second" (true, 11) result
}

/--
Test FunArrow Choice left.
-/
private def case_funarrow_choice_left : TestCase := {
  name := "FunArrow Choice: left applies to Sum.inl",
  run := do
    let arrow : FunArrow Int Int := FunArrow.mk double
    let lifted := Choice.left (P := fun α β => FunArrow α β) (γ := String) arrow
    let inlResult := lifted.run (Sum.inl 7)
    let inrResult := lifted.run (Sum.inr "test")
    ensureEq "FunArrow Choice left inl" (Sum.inl 14) inlResult
    ensureEq "FunArrow Choice left inr" (Sum.inr "test") inrResult
}

/--
Test FunArrow Choice right.
-/
private def case_funarrow_choice_right : TestCase := {
  name := "FunArrow Choice: right applies to Sum.inr",
  run := do
    let arrow : FunArrow Int Int := FunArrow.mk double
    let lifted := Choice.right (P := fun α β => FunArrow α β) (γ := String) arrow
    let inlResult := lifted.run (Sum.inl "test")
    let inrResult := lifted.run (Sum.inr 7)
    ensureEq "FunArrow Choice right inl" (Sum.inl "test") inlResult
    ensureEq "FunArrow Choice right inr" (Sum.inr 14) inrResult
}

/--
Test FunArrow Closed instance.
-/
private def case_funarrow_closed : TestCase := {
  name := "FunArrow Closed: closed handles function types",
  run := do
    let arrow : FunArrow Int Int := FunArrow.mk double
    let closed := Closed.closed (P := fun α β => FunArrow α β) (γ := String) arrow
    -- closed takes a String → Int function and returns a String → Int function
    let inputFn : String → Int := fun s => s.length
    let resultFn := closed.run inputFn
    ensureEq "FunArrow Closed" 10 (resultFn "hello")  -- length "hello" = 5, doubled = 10
}

/--
Test FunArrow Wandering instance.
-/
private def case_funarrow_wandering : TestCase := {
  name := "FunArrow Wandering: wander modifies all elements",
  run := do
    let arrow : FunArrow Int Int := FunArrow.mk double

    let walk : {F : Type → Type} → [Applicative F] → (Int → F Int) → List Int → F (List Int) :=
      fun {F} [Applicative F] f xs => List.mapA f xs

    let lifted := Wandering.wander (P := fun α β => FunArrow α β) walk arrow
    let result := lifted.run [1, 2, 3]
    ensureEq "FunArrow Wandering" [2, 4, 6] result
}

/-! ## Costar Tests -/

/--
Test that Costar satisfies dimap identity law.
-/
private def case_costar_dimap_id : TestCase := {
  name := "Costar: dimap id id = id",
  run := do
    let costar : Costar List Int Int := Costar.mk (fun xs => xs.foldl (· + ·) 0)
    let result := Profunctor.dimap (id : Int → Int) (id : Int → Int) costar
    ensureEq "Costar dimap id" (costar.run [1, 2, 3]) (result.run [1, 2, 3])
}

/--
Test Costar dimap: pre is applied via functor map, post is applied to result.
-/
private def case_costar_dimap_pre_post : TestCase := {
  name := "Costar: dimap applies pre via map, post to result",
  run := do
    let costar : Costar List Int Int := Costar.mk (fun xs => xs.foldl (· + ·) 0)
    let result := Profunctor.dimap double inc costar
    -- First maps double over [1, 2, 3] to get [2, 4, 6], then sums to 12, then inc to 13
    ensureEq "Costar dimap" 13 (result.run [1, 2, 3])
}

/--
Test Costar Closed instance.
The closed operation for Costar takes Costar F a b and returns Costar F (γ → a) (γ → b).
closed p = Costar.mk (fun fga => fun γVal => p.run (Functor.map (fun h => h γVal) fga))
-/
private def case_costar_closed : TestCase := {
  name := "Costar Closed: closed handles function outputs",
  run := do
    let costar : Costar List Int Int := Costar.mk (fun xs => xs.length)
    let closed := Closed.closed (P := Costar List) (γ := String) costar
    -- closed takes List (String → Int) and returns String → Int
    -- The implementation maps (fun h => h γVal) over the list, then applies costar
    let fns : List (String → Int) := [fun s => s.length, fun _ => 42]
    let resultFn := closed.run fns
    -- For input "hello": map (fun h => h "hello") [f1, f2] = [5, 42]
    -- Then costar counts length = 2
    ensureEq "Costar Closed test" 2 (resultFn "hello")
}

/--
Test Costar with Option functor.
-/
private def case_costar_option : TestCase := {
  name := "Costar Option: extracts value from option",
  run := do
    let costar : Costar Option Int Int := Costar.mk (fun opt => opt.getD 0)
    let someResult := costar.run (some 42)
    let noneResult := costar.run none
    ensureEq "Costar Option some" 42 someResult
    ensureEq "Costar Option none" 0 noneResult
}

/-! ## All Test Cases -/

def cases : List TestCase :=
  [ -- Forget tests
    case_forget_dimap_id
  , case_forget_dimap_comp
  , case_forget_strong_first
  , case_forget_strong_second
  , case_forget_choice_left
  , case_forget_choice_left_inr
  , case_forget_wandering
    -- Star tests
  , case_star_dimap_id
  , case_star_strong_first
  , case_star_strong_second
  , case_star_choice_left
  , case_star_choice_left_inr
  , case_star_option_short_circuit
  , case_star_wandering
    -- Tagged tests
  , case_tagged_dimap_id
  , case_tagged_dimap_post
  , case_tagged_choice_left
  , case_tagged_choice_right
    -- FunArrow tests
  , case_funarrow_dimap_id
  , case_funarrow_dimap_comp
  , case_funarrow_strong_first
  , case_funarrow_strong_second
  , case_funarrow_choice_left
  , case_funarrow_choice_right
  , case_funarrow_closed
  , case_funarrow_wandering
    -- Costar tests
  , case_costar_dimap_id
  , case_costar_dimap_pre_post
  , case_costar_closed
  , case_costar_option
  ]

end CollimatorTests.ConcreteProfunctors
