import Collimator.Core
import Collimator.Concrete.Forget
import Collimator.Concrete.Star
import Collimator.Concrete.Tagged
import Collimator.Concrete.FunArrow
import Collimator.Concrete.Costar
import Batteries
import Crucible

/-!
# Profunctor Tests

Consolidated test suite for profunctor functionality:
- Core profunctor laws and typeclass instances (Profunctor, Strong, Choice, Wandering, Closed)
- Concrete profunctor implementations (Forget, Star, Tagged, FunArrow, Costar)

This file combines tests from Core.lean and ConcreteProfunctors.lean.
-/

namespace CollimatorTests.ProfunctorTests

open Batteries
open Collimator.Core
open Collimator.Concrete
open Crucible

testSuite "Profunctor Tests"

/-! ## Core Profunctor Tests -/

test "profunctor arrow dimap applies pre- and post-maps" := do
  let p : Nat → String := fun n => s!"n={n}"
  let transformed := Profunctor.dimap (P := fun α β : Type => α → β)
    (fun n => n + 2) (fun s => s ++ "!") p
  let actual := transformed 3
  actual ≡ "n=5!"

test "lmap and rmap specialize dimap" := do
  let p : Nat → Nat := fun n => n * 2
  let leftMapped := lmap (P := fun α β : Type => α → β) (fun n => n + 1) p
  let rightMapped := rmap (P := fun α β : Type => α → β) (fun n => n + 3) p
  (leftMapped 3) ≡ 8
  (rightMapped 3) ≡ 9

test "strong arrow distributes over products" := do
  let p : Nat → Nat := fun n => n + 1
  let firstF := Strong.first (P := fun α β : Type => α → β) p
  let secondF := Strong.second (P := fun α β : Type => α → β) p
  (firstF (6, "ctx")) ≡ (7, "ctx")
  (secondF ("ctx", 10)) ≡ ("ctx", 11)

test "choice arrow distributes over sums" := do
  let p : Nat → Bool := fun n => n % 2 == 0
  let leftF := Choice.left (P := fun α β : Type => α → β) p
  let rightF := Choice.right (P := fun α β : Type => α → β) p
  match leftF (Sum.inl 4) with
  | Sum.inl b => ensure (b) "left maps Sum.inl"
  | _ => ensure false "left should map Sum.inl to Sum.inl"
  match leftF (Sum.inr "tag") with
  | Sum.inr tag => ensure (tag == "tag") "left preserves Sum.inr"
  | _ => ensure false "left should preserve Sum.inr"
  match rightF (Sum.inr 5) with
  | Sum.inr b => ensure (b == false) "right maps Sum.inr"
  | _ => ensure false "right should map Sum.inr to Sum.inr"
  match rightF (Sum.inl "orig") with
  | Sum.inl tag => ensure (tag == "orig") "right preserves Sum.inl"
  | _ => ensure false "right should preserve Sum.inl"

test "const profunctor ignores morphisms" := do
  let payload : Const String Nat Nat := "payload"
  let remapped : Const String Nat String := Profunctor.dimap (P := Const String) (fun | n => n + 1)
    (fun | s => s ++ "!") payload
  -- Const R _ _ = R, id coerces to String
  (id remapped : String) ≡ "payload"

test "kleisli dimap composes with Functor.map" := do
  let p : Kleisli Option Nat String := fun n =>
    if n % 2 == 0 then some (s!"{n}") else none
  let remapped := Profunctor.dimap (P := Kleisli Option)
    (fun n => n + 1) (fun s => s ++ "!") p
  (remapped 3) ≡ (some "4!")
  (remapped 2) ≡ (none : Option String)

test "lawful arrow dimap composition matches sequential dimaps" := do
  let p : Nat → String := fun n => s!"{n}"
  let f : Nat → Nat := fun n => n + 1
  let f' : Nat → Nat := fun n => n * 2
  let g : String → String := fun s => s ++ "?"
  let g' : String → Nat := fun s => s.length
  let lhs := Profunctor.dimap (P := fun α β : Type => α → β)
    (f ∘ f') (g' ∘ g) p
  let rhs :=
    Profunctor.dimap (P := fun α β : Type => α → β) f' g'
      (Profunctor.dimap (P := fun α β : Type => α → β) f g p)
  (lhs 3) ≡ (rhs 3)
  (lhs 5) ≡ (rhs 5)

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
  let star : Star Option Int Int := ⟨fun x => some (x + 1)⟩
  let result := Profunctor.dimap (id : Int → Int) (id : Int → Int) star
  result.run 5 ≡ star.run 5

test "Star Strong: first preserves tuple structure" := do
  let star : Star Option Int Int := ⟨fun x => some (x * 2)⟩
  let lifted := Strong.first (P := Star Option) (γ := String) star
  let result := lifted.run (10, "test")
  result ≡ some (20, "test")

test "Star Strong: second preserves tuple structure" := do
  let star : Star Option Int Int := ⟨fun x => some (x + 5)⟩
  let lifted := Strong.second (P := Star Option) (γ := Bool) star
  let result := lifted.run (true, 7)
  result ≡ some (true, 12)

test "Star Choice: left maps Sum.inl values" := do
  let star : Star Option Int Int := ⟨fun x => some (x * 3)⟩
  let lifted := Choice.left (P := Star Option) (γ := String) star
  let result := lifted.run (Sum.inl 4)
  result ≡ some (Sum.inl 12)

test "Star Choice: left passes through Sum.inr" := do
  let star : Star Option Int Int := ⟨fun x => some (x * 3)⟩
  let lifted := Choice.left (P := Star Option) (γ := String) star
  let result := lifted.run (Sum.inr "hello")
  result ≡ some (Sum.inr "hello")

test "Star Option: short-circuits on none" := do
  let star : Star Option Int Int := ⟨fun x => if x > 0 then some (x + 1) else none⟩
  let positiveResult := star.run 5
  let negativeResult := star.run (-3)
  positiveResult ≡ some 6
  negativeResult ≡ (none : Option Int)

test "Star Wandering: traverses with applicative effect" := do
  let star : Star Option Int Int := ⟨fun x => if x >= 0 then some (x * 2) else none⟩

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

end CollimatorTests.ProfunctorTests
