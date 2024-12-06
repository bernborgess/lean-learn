import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Fin.Tuple.Reflection
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

def k : Fin 3 → Nat := ![1,2,3]

#eval ![2,3,4] + ![1,5,3]
#eval ![2,3,4] - ![1,5,3]
#eval ![1,0,1] * ![3,4,5]
#eval ![3,6,3] / ![3,3,3]
#eval FinVec.sum $ ![1,3,4] * ![1,0,1]

-- notation:35 "∑" thelist:30 => FinVec.sum thelist
namespace Dvorak

open BigOperators

def a := ![1,2,3]
def s := ![true,true,true]

variable {p₁ p₂ p₃ : Bool}
-- def x := ![p₁,p₂,p₃]
def x := ![false,true,false]
def x' := ![p₁,p₂,p₃]

def k := ∑ i, a i * (if s i = x i then 1 else 0)

#eval k

@[simp]
abbrev pbSum' {n : ℕ} (a : Fin n → ℤ) (s x : Fin n → Bool) : ℤ :=
  ∑ i, a i * (if s i = x i then 1 else 0)

open scoped Matrix

-- 3w + 6x + 6y + 2z ≥ 9
def t3 := pbSum' ![3,6,6,2] ![false,false,false,false] ≥ 9

-- 2!z ≥ 0
def t4 := pbSum' ![0,0,0,2] ![false,false,false,true] ≥ 0

-- 3w + 6x + 6y ≥ 7


open BigOperators

def pbSum {n : ℕ} (a : Fin n → ℤ) (s x : Fin n → Bool) : ℤ :=
  ∑ i, a i * (if s i = x i then 1 else 0)

structure Condition (n : ℕ) where
  weights : Fin n → ℤ
  rhs : ℤ

def Condition.eval {n : ℕ} (C : Condition n) (x : Fin n → Bool) : ℤ :=
  ∑ i, if x i then C.weights i else 0

def Condition.IsSatisfied {n : ℕ} (C : Condition n) (x : Fin n → Bool) : Prop :=
  C.eval x ≥ C.rhs

def condition_of_signs {n : ℕ} (w : Fin n → ℤ) (s : Fin n → Bool) (r : ℤ) : Condition n :=
  Condition.mk (fun i => if s i then w i else -(w i)) (r - ∑ i, if s i then 0 else w i)

lemma condition_of_signs_eval_eq_pbSum_minus {n : ℕ}
    (w : Fin n → ℤ) (s : Fin n → Bool) (r : ℤ) (x : Fin n → Bool) :
    (condition_of_signs w s r).eval x = pbSum w s x - ∑ i, if s i then 0 else w i := by
  unfold condition_of_signs
  unfold Condition.eval
  unfold pbSum
  apply eq_sub_of_add_eq
  apply eq_of_sub_eq_zero
  rw [←Finset.sum_add_distrib]
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_eq_zero
  intro i _
  cases x i <;> cases hsi : s i <;> simp [hsi]

theorem condition_of_signs_IsSatisfied_iff_pbSum_ge {n : ℕ}
    (w : Fin n → ℤ) (s : Fin n → Bool) (r : ℤ) (x : Fin n → Bool) :
    (condition_of_signs w s r).IsSatisfied x ↔ pbSum w s x ≥ r := by
  unfold Condition.IsSatisfied
  rw [condition_of_signs_eval_eq_pbSum_minus]
  unfold condition_of_signs
  simp

def addConditions {n : ℕ} (a b : Condition n) : Condition n :=
  Condition.mk (a.weights + b.weights) (a.rhs + b.rhs)

theorem addConditions_IsSatisfied {n : ℕ} {a b : Condition n} {x : Fin n → Bool}
    (ha : a.IsSatisfied x) (hb : b.IsSatisfied x) :
    (addConditions a b).IsSatisfied x := by
  unfold addConditions
  simp [Condition.IsSatisfied, Condition.eval] at *
  convert Int.add_le_add ha hb
  rw [←Finset.sum_add_distrib]
  congr
  ext i
  cases x i <;> simp


end Dvorak


namespace Struct

structure Variable where
  name : String
  coeff : Int
 deriving Repr

def w : Variable := { name := "w", coeff := 1 }
def x : Variable := { name := "x", coeff := 2 }
def y : Variable := { name := "y", coeff := 1 }
#eval w

def List.sum : List Int → Int := List.foldl (·+·) 0

structure Expr where
  vars : List Variable
  const : Int
 deriving Repr

def someExpr : Expr := {
  vars := [w,x,y]
  const := 2
}

-- w + 2x + y ≥ 2
#eval someExpr


def Expr.eval : Expr → List Int → Bool:=
  λ {vars,const} => λ values =>
  have coeffs := vars.map (·.coeff)
  have sumProduct := (coeffs.zipWith (·*·) values).sum
  sumProduct >= const

-- 0 + 2 + 0 ≥ 2
#eval someExpr.eval [0,1,0]


end Struct


namespace Induct

inductive Variable where
| Var : String → Variable
| NegVar : String → Variable
deriving Repr

inductive Term where
| Term : Int → Variable → Term
deriving Repr

inductive Expr where
| Expr : List Term → Int → Expr
deriving Repr

-- x₁ + 2!x₂ + 3x₃ + 4!x₄ + 5x₅ ≥ 7
def exampleExpr : Expr := .Expr [
    .Term 1 (.Var "x1"),
    .Term 2 (.NegVar "x2"),
    .Term 3 (.Var "x3"),
    .Term 4 (.NegVar "x4"),
    .Term 5 (.Var "x5"),
  ] 7

def Expr.eval (expr : Induct.Expr) (xs : List Int) : Bool :=
  match expr with
  | .Expr ts const =>
    have coeffs := ts.map (λ (.Term x _) => x)
    (coeffs.zipWith (·*·) xs).sum >= const

end Induct


namespace Agda

abbrev Variable := ℤ
abbrev Coefficient := ℤ
abbrev Constant := ℤ
abbrev LinearTerm := Coefficient × Variable
abbrev LinearInequality := List LinearTerm × Constant

def evalTerm : LinearTerm → ℤ → ℤ :=
  λ (c,_) v => c * v

def evalLHS : List LinearTerm → List ℤ → ℤ
| [], [] => 0
| (t::ts),(v::vs) => evalTerm t v + evalLHS ts vs
| _, _ => 0

def satisfies : LinearInequality → List ℤ → Bool
| (terms,const), values => evalLHS terms values ≥ const

def li : LinearInequality := ([1,2,1],3)

#eval li

end Agda


/-!
# A Convenient Suggestion

* We want to model Pseudo-Boolean (PB) formulas
  in order to decide whether `F` is `satisfiable`/`feasible`
  (Pseudo-Boolean format is richer than conjunctive normal for (CNF))

* Pseudo-Boolean Optimization (PBO) is
  Find satisfying assignment to `F` that `minimizes` the
  `objective function ∑ᵢ wᵢlᵢ`
https://jakobnordstrom.se/docs/presentations/TalkSimons2102_PseudoBooleanSolvingLiveTalk.pdf

* Pseudo-Boolean constraints are 0-1 integer linear constraints
    ∑ᵢ  aᵢlᵢ ⋈ A
  where
  - ⋈ ∈ {≥,≤,=,>,<}
  - aᵢ,A ∈ ℤ
  - `literals` lᵢ : xᵢ or !xᵢ (where xᵢ + !xᵢ = 1) // Using ! for \overline

[Bar95] Peter Barth. A Davis-Putnam based enumeration algorithm for linear
pseudo-Boolean optimization. Technical Report MPI-I-95-2-003,
Max-Planck-Institut fuer Informatik, January 1995.
https://hdl.handle.net/11858/00-001M-0000-0014-A1C6-1
* It is convenient to use `normalized form` [Bar95] (without loss of generality)
    ∑ᵢ aᵢlᵢ ≥ A
  where
  - constraint is always greater-than-or-equal
  - aᵢ, A ∈ ℕ
  - A = deg(∑ᵢ aᵢlᵢ ≥ A) referred to as `degree (of falsity)`
-/

/-!
# Keeping Positive
"Keep your values positive because your values become your destiny." - Mahatma Gandhi

* For every occurence of a negated x:  α !x ≥ A
  we can expand the definiton of negated literal:

1.  α !x ≥ A              Assum.
2.  α (1 - x) ≥ A         Definition of negate literal
3.  α - αx ≥ A            Distributivity
4.  -α x ≥ A - α          Subtract both side by α
5.  β x ≥ B               where β := -α, B := A - α

* Now we may work with positive literals only, converting before creating the Expression

-/

/-!
# Conversion to Normalized Form: Example
https://jakobnordstrom.se/docs/presentations/TalkSimons2102_PseudoBooleanSolvingTutorial.pdf

* Normalized form used for convenience and without loss of generality

  -x₁ + 2x₂ - 3x₃ + 4x₄ - 5x₅ < 0

1. Make inequality non-strict

  -x₁ + 2x₂ - 3x₃ + 4x₄ - 5x₅ ≤ -1

2. Multiply by -1 to get greater-than-or-equal

  x₁ - 2x₂ + 3x₃ - 4x₄ + 5x₅

3. Replace -l by -(1 - !l) [where we define !!x ≐ x]

  x₁ - 2(1 - !x₂) + 3x₃ - 4(1 - !x₄) + 5x₅ ≥ 1
  x₁ + 2!x₂ + 3x₃ + 4!x₄ + 5x₅ ≥ 7

4. Replace "=" by two inequalities "≥" and "≤"


-/
