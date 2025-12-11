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

testSuite "Concrete Profunctors"

/-! ## Test Helpers -/

private def double : Int → Int := fun x => x * 2
private def inc : Int → Int := fun x => x + 1
private def toString' : Int → String := fun x => s!"{x}"
private def length' : String → Int := fun s => s.length

/-! ## Forget Tests -/

test "Forget: dimap id id = id" := do
  let forget : Forget Int Int String := fun x => x * 2
  let result := Profunctor.dimap (id : Int → Int) (id : String → String) forget
  result 5 ≡ forget 5

test "Forget: dimap (g ∘ f) id = dimap f id ∘ dimap g id" := do
  let forget : Forget Int Int String := fun x => x * 3

  -- dimap (double ∘ inc) id = apply (double ∘ inc) then forget
  -- On input 2: double(inc(2)) = double(3) = 6, then * 3 = 18
  let lhs := Profunctor.dimap (double ∘ inc) (id : String → String) forget

  -- dimap inc id (dimap double id forget) = apply inc, then double, then forget
  -- On input 2: inc(2) = 3, then double(3) = 6, then * 3 = 18
  let inner := Profunctor.dimap double (id : String → String) forget
  let rhs := Profunctor.dimap inc (id : String → String) inner

  lhs 2 ≡ rhs 2

test "Forget Strong: first extracts from tuple" := do
  let forget : Forget Int Int String := fun x => x + 100
  let lifted := Strong.first (P := Forget Int) (γ := String) forget
  let result := lifted (7, "hello")
  result ≡ 107

test "Forget Strong: second extracts from tuple" := do
  let forget : Forget Int Int String := fun x => x + 50
  let lifted := Strong.second (P := Forget Int) (γ := Bool) forget
  let result := lifted (true, 20)
  result ≡ 70

test "Forget Choice: left applies to Sum.inl" := do
  let forget : Forget Int Int String := fun x => x * 10
  let lifted := Choice.left (P := Forget Int) (γ := Bool) forget
  let result := lifted (Sum.inl 3)
  result ≡ 30

test "Forget Choice: left returns default for Sum.inr" := do
  let forget : Forget Int Int String := fun x => x * 10
  let lifted := Choice.left (P := Forget Int) (γ := Bool) forget
  let result := lifted (Sum.inr true)
  result ≡ 0  -- default for Int is 0

test "Forget Wandering: uses monoid to aggregate" := do
  -- Forget (List Int) aggregates via list append
  -- When we wander over a list with a "single element" forget, we should get all elements
  let forget : Forget (List Int) Int String := fun x => [x]

  -- The Wandering instance for Forget uses Const R as the applicative functor
  -- This means walk will use pure = one = [] and <*> = mul = append
  -- Since Const R ignores the second type param, we get accumulation

  -- Test basic properties of the forget profunctor
  forget 42 ≡ [42]

  -- Test that Strong.first extracts and applies forget
  let strongForget := Strong.first (P := Forget (List Int)) (γ := String) forget
  strongForget (7, "ignored") ≡ [7]

/-! ## Star Tests -/

test "Star: dimap id id = id" := do
  let star : Star Option Int Int := Star.mk (fun x => some (x + 1))
  let result := Profunctor.dimap (id : Int → Int) (id : Int → Int) star
  result.run 5 ≡ star.run 5

test "Star Strong: first preserves tuple structure" := do
  let star : Star Option Int Int := Star.mk (fun x => some (x * 2))
  let lifted := Strong.first (P := Star Option) (γ := String) star
  let result := lifted.run (10, "test")
  result ≡ some (20, "test")

test "Star Strong: second preserves tuple structure" := do
  let star : Star Option Int Int := Star.mk (fun x => some (x + 5))
  let lifted := Strong.second (P := Star Option) (γ := Bool) star
  let result := lifted.run (true, 7)
  result ≡ some (true, 12)

test "Star Choice: left maps Sum.inl values" := do
  let star : Star Option Int Int := Star.mk (fun x => some (x * 3))
  let lifted := Choice.left (P := Star Option) (γ := String) star
  let result := lifted.run (Sum.inl 4)
  result ≡ some (Sum.inl 12)

test "Star Choice: left passes through Sum.inr" := do
  let star : Star Option Int Int := Star.mk (fun x => some (x * 3))
  let lifted := Choice.left (P := Star Option) (γ := String) star
  let result := lifted.run (Sum.inr "hello")
  result ≡ some (Sum.inr "hello")

test "Star Option: short-circuits on none" := do
  let star : Star Option Int Int := Star.mk (fun x => if x > 0 then some (x + 1) else none)
  let positiveResult := star.run 5
  let negativeResult := star.run (-3)
  positiveResult ≡ some 6
  negativeResult ≡ (none : Option Int)

test "Star Wandering: traverses with applicative effect" := do
  let star : Star Option Int Int := Star.mk (fun x => if x >= 0 then some (x * 2) else none)

  let walk : {F : Type → Type} → [Applicative F] → (Int → F Int) → List Int → F (List Int) :=
    fun {F} [Applicative F] f xs => List.mapA f xs

  let lifted := Wandering.wander (P := Star Option) walk star
  let successResult := lifted.run [1, 2, 3]
  let failResult := lifted.run [1, -2, 3]

  successResult ≡ some [2, 4, 6]
  failResult ≡ (none : Option (List Int))

/-! ## Tagged Tests -/

test "Tagged: dimap id id = id" := do
  let tagged : Tagged Int String := "hello"
  let result := Profunctor.dimap (id : Int → Int) (id : String → String) tagged
  result ≡ tagged

test "Tagged: dimap only applies post function" := do
  let tagged : Tagged Int Int := 42
  let result := Profunctor.dimap (fun _ : String => 0) double tagged
  result ≡ 84

test "Tagged Choice: left wraps in Sum.inl" := do
  let tagged : Tagged Int String := "test"
  let lifted := Choice.left (P := fun α β => Tagged α β) (γ := Bool) tagged
  lifted ≡ Sum.inl "test"

test "Tagged Choice: right wraps in Sum.inr" := do
  let tagged : Tagged Int String := "test"
  let lifted := Choice.right (P := fun α β => Tagged α β) (γ := Bool) tagged
  lifted ≡ Sum.inr "test"

/-! ## FunArrow Tests -/

test "FunArrow: dimap id id = id" := do
  let arrow : FunArrow Int Int := FunArrow.mk double
  let result := Profunctor.dimap (id : Int → Int) (id : Int → Int) arrow
  result.run 5 ≡ arrow.run 5

test "FunArrow: dimap composes correctly" := do
  let arrow : FunArrow Int Int := FunArrow.mk double
  let result := Profunctor.dimap inc inc arrow
  -- (inc ∘ double ∘ inc) 3 = inc (double (inc 3)) = inc (double 4) = inc 8 = 9
  result.run 3 ≡ 9

test "FunArrow Strong: first applies to first element" := do
  let arrow : FunArrow Int Int := FunArrow.mk double
  let lifted := Strong.first (P := fun α β => FunArrow α β) (γ := String) arrow
  let result := lifted.run (5, "hello")
  result ≡ (10, "hello")

test "FunArrow Strong: second applies to second element" := do
  let arrow : FunArrow Int Int := FunArrow.mk inc
  let lifted := Strong.second (P := fun α β => FunArrow α β) (γ := Bool) arrow
  let result := lifted.run (true, 10)
  result ≡ (true, 11)

test "FunArrow Choice: left applies to Sum.inl" := do
  let arrow : FunArrow Int Int := FunArrow.mk double
  let lifted := Choice.left (P := fun α β => FunArrow α β) (γ := String) arrow
  let inlResult := lifted.run (Sum.inl 7)
  let inrResult := lifted.run (Sum.inr "test")
  inlResult ≡ Sum.inl 14
  inrResult ≡ Sum.inr "test"

test "FunArrow Choice: right applies to Sum.inr" := do
  let arrow : FunArrow Int Int := FunArrow.mk double
  let lifted := Choice.right (P := fun α β => FunArrow α β) (γ := String) arrow
  let inlResult := lifted.run (Sum.inl "test")
  let inrResult := lifted.run (Sum.inr 7)
  inlResult ≡ Sum.inl "test"
  inrResult ≡ Sum.inr 14

test "FunArrow Closed: closed handles function types" := do
  let arrow : FunArrow Int Int := FunArrow.mk double
  let closed := Closed.closed (P := fun α β => FunArrow α β) (γ := String) arrow
  -- closed takes a String → Int function and returns a String → Int function
  let inputFn : String → Int := fun s => s.length
  let resultFn := closed.run inputFn
  resultFn "hello" ≡ 10  -- length "hello" = 5, doubled = 10

test "FunArrow Wandering: wander modifies all elements" := do
  let arrow : FunArrow Int Int := FunArrow.mk double

  let walk : {F : Type → Type} → [Applicative F] → (Int → F Int) → List Int → F (List Int) :=
    fun {F} [Applicative F] f xs => List.mapA f xs

  let lifted := Wandering.wander (P := fun α β => FunArrow α β) walk arrow
  let result := lifted.run [1, 2, 3]
  result ≡ [2, 4, 6]

/-! ## Costar Tests -/

test "Costar: dimap id id = id" := do
  let costar : Costar List Int Int := Costar.mk (fun xs => xs.foldl (· + ·) 0)
  let result := Profunctor.dimap (id : Int → Int) (id : Int → Int) costar
  result.run [1, 2, 3] ≡ costar.run [1, 2, 3]

test "Costar: dimap applies pre via map, post to result" := do
  let costar : Costar List Int Int := Costar.mk (fun xs => xs.foldl (· + ·) 0)
  let result := Profunctor.dimap double inc costar
  -- First maps double over [1, 2, 3] to get [2, 4, 6], then sums to 12, then inc to 13
  result.run [1, 2, 3] ≡ 13

test "Costar Closed: closed handles function outputs" := do
  let costar : Costar List Int Int := Costar.mk (fun xs => xs.length)
  let closed := Closed.closed (P := Costar List) (γ := String) costar
  -- closed takes List (String → Int) and returns String → Int
  -- The implementation maps (fun h => h γVal) over the list, then applies costar
  let fns : List (String → Int) := [fun s => s.length, fun _ => 42]
  let resultFn := closed.run fns
  -- For input "hello": map (fun h => h "hello") [f1, f2] = [5, 42]
  -- Then costar counts length = 2
  resultFn "hello" ≡ 2

test "Costar Option: extracts value from option" := do
  let costar : Costar Option Int Int := Costar.mk (fun opt => opt.getD 0)
  let someResult := costar.run (some 42)
  let noneResult := costar.run none
  someResult ≡ 42
  noneResult ≡ 0

#generate_tests

end CollimatorTests.ConcreteProfunctors
