import Mathlib.Tactic.LibrarySearch -- exact?
import Mathlib.Algebra.BigOperators.Basic

/-! # Pseudo-Boolean Reasoning: Cutting Planes

* Input axioms

* Literal axioms
=> lᵢ ≥ 0

* Addition
Σᵢ aᵢlᵢ ≥ A   Σᵢ bᵢlᵢ ≥ B
=> Σ(aᵢ+bᵢ)lᵢ ≥ A + B

* Multiplication for any c ∈ ℕ⁺
Σᵢ aᵢlᵢ ≥ A
=> Σᵢ caᵢlᵢ ≥ cA

* Division for any c ∈ ℕ⁺ (constraint in normalized form)
Σᵢ aᵢlᵢ ≥ A
=> Σᵢ ceil(aᵢ/c)lᵢ ≥ ceil(A/c)

-/

-- Todo: How to model a summation?
-- How many values are i values?
-- How to keep the lᵢ values as free variables? (lazyness?)

/-!
# To build a value of type "PB" we need

* aᵢ i values of type Nat
* lᵢ i values of type Fin 2 = {0,1}
* A one value of type Nat
⊢
 Σ aᵢlᵢ ≥ A

-/

-- The constructor also needs the proof that this holds.
-- Todo: fix i = as.length = ls.length
-- Todo: implement HMul for the lists.
-- structure PB (as : List Nat) (ls : List (Fin 2)) (A : Nat) where
--  summation : as * ls ≥ A

-- Haniel Barbosa:
-- 1. Define the statements of the theorems corresponding to the rules
--  of cutting planes calculus.
-- Have them as axioms, or proven using sorry.

-- Σᵢ(aᵢ*lᵢ)
def pbSum (as : List Int) (ls : List Int) : Int := (as.zipWith (·*·) ls).foldl (·+·) 0

#eval pbSum [3,2] [1]
-- Σᵢ aᵢlᵢ ≥ A   Σᵢ bᵢlᵢ ≥ B
-- => Σ(aᵢ+bᵢ)lᵢ ≥ A + B
theorem addition : ∀ {A B : Int} {as ls bs : List Int},
                      (pbSum as ls) ≥ A →
                      (pbSum bs ls) ≥ B →
                      (pbSum (as.zipWith (·+·) bs) ls) ≥ (A + B) := sorry

/-!
Todo: No guarantees (type-level) that:
* ∀ l in ls, l ∈ {0,1}
* ls.length == as.length == bs.length
-/

theorem t1 : pbSum [3,2,9] [1,1,0] ≥ 3 := by
  exact Int.NonNeg.mk (0 + 3 * 1 + 2 * 1 - Nat.succ 2)
  done

theorem t2 : pbSum [2,3,3] [1,1,0] ≥ 2 := by
  exact Int.NonNeg.mk (0 + 2 * 1 + 3 * 1 - Nat.succ 1)
  done

-- Goal is
-- pbSum ([3,2,9].zipWith (·+·) [2,3,3]) [1,1,0] ≥ 3 + 2
-- ≡ pbSum [5,5,12] [1,1,0] ≥ 3 + 2
-- ≡ 10 ≥ 3 + 2
-- ≡ 10 ≥ 5

theorem t3 : pbSum [5,5,12] [1,1,0] ≥ 3 + 2 := by
  exact addition t1 t2
  done

-- 2. Write the example in Jakob's slide such that "sorry" is replaced
--  by the applications of the rules in the example:
namespace JakobExample

def w : Int := 1
def x : Int := 0
def y : Int := 1
def z : Int := 0

def ls := [w,x,y,z]

-- ! Reframe -z as "not". With z=0, should yield 1

theorem ex (t1 : pbSum [1,2,1,0] ls ≥ 2) -- (w + 2 * x + y ≥ 2) →
           (t2 : pbSum [1,2,4,2] ls ≥ 5) -- (w + 2 * x + 4 * y + 2 * z ≥ 5) →
           (t3 : pbSum [0,0,0,-1] ls ≥ -1) -- (-z ≥ 0) →
           : pbSum [1,2,2,0] ls ≥ 3 -- (w + 2 * x + 2 * y ≥ 3) := by
           := by
  have h1 : pbSum [2,4,2,0] ls ≥ 4    := addition t1 t1
  have h2 : pbSum [3,6,6,2] ls ≥ 9    := addition h1 t2
  have h3 : pbSum [0,0,0,-2] ls ≥ -2  := addition t3 t3
  have h4 : pbSum [3,6,6,0] ls  ≥ 7   := addition h3 h2
  sorry
  done

end JakobExample

-- f̅
-- Once this is done, then the next step would be to prove the actual
--  theorems corresponding to the rules

example {x : Nat} : x + x = 2 * x := by
  have h : 2 * x = x + x := Nat.two_mul x
  rw [h]
  done

example {x : Nat} (hnz : 0 < x) : x < 2 * x := by
  rw [Nat.two_mul]              -- ⊢ x < 2 * x
  apply Nat.lt_add_of_pos_left  -- ⊢ x < x + x
  exact hnz                     -- ⊢ 0 < x
  done

-- ∑

namespace CP

variable {goal : Prop}

def Multiplication {x y : Int}
  (k : Int)
  (h1 : x ≥ y)
  : goal := sorry

def Addition
  {w x y z : Int}
  (h1 : w ≥ x)
  (h2 : y ≥ z)
  : goal := sorry

def Dissolve
  {w x : Int}
  (h1 : w ≥ x)
  : goal := sorry

def Division
  {w x : Int}
  (k : Int)
  (h1 : w ≥ x)
  : goal := sorry

end CP

notation:71 "‽" arg:70 => arg

section Expectation

example {w x y z : Int}
  (h1 : w + 2*x + y ≥ 2)
  (h2 : w + 2*x + 4*y + 2*z ≥ 5)
  (h3 : ‽z ≥ 0)
  : w + 2*x + 2*y ≥ 3 := by
  have h4 : 2*w + 4*x + 2*y ≥ 4               := by exact CP.Multiplication 2 h1
  have h5 : 3*w + 6*x + 6*y + 2*z ≥ 9         := by exact CP.Addition h4 h2
  have h6 : 2*‽z ≥ 0                          := by exact CP.Multiplication 2 h3
  have h7 : 3*w + 6*x + 6*y + 2*z + 2*‽z ≥ 9  := by exact CP.Addition h5 h6
  have h8 : 3*w + 6*x + 6*y ≥ 7               := by exact CP.Dissolve h7
  have h9 : w + 2*x + 2*y ≥ 3                 := by exact CP.Division 3 h8
  exact h9
  done

end Expectation
