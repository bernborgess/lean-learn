import Lean
import Mathlib.Tactic.Linarith

/-!

# Proof by reflection

You may have noticed that we can't prove anything aboud the tactics we write :(
But there's a middle ground: sometimes with a bit of meta "wrapper code"
we can turn proofs aboud syntax-like operations into actual proof terms!

The general strategy looks like this:
* represent the syntax of some class of formulas in (non-meta) Lean
* define an interpretation function from these formulas to `Prop`
* define some operation on this syntax, and prove it correct with respect to the interpretation
* write a small bit of meta code that turns a goal into a statement about your reflected syntax

The idea is that the goal left after applying your correctness theorem can be proved by computation.

This is commonly used for evaluation or normalization functions.
`ring`, for example, can be implemented by defining the syntax of ring expressions
and verifying a normalization algorithm:

if
`ring_syntax : Type`,
`interp {α : Type} [ring α] : ring_syntax → α`
`normalize : ring_syntax → ring_syntax`, then
`∀ r1 r2 : ring_syntax, interp r1 = interp r2 ↔ normalize r1 = normalize r2`.

The meta code looks at a goal `c + a*b = b*a + c`,
constructs `ring_syntax` objects `r1` and `r2` representing both sides,
and changes the goal to showing that `normalize r1 = normalize r2`.
This can be proved by `refl`.

-/

inductive bexpr
| atom : Bool → bexpr
| and : bexpr → bexpr → bexpr
| or : bexpr → bexpr → bexpr
| imp : bexpr → bexpr → bexpr
| not : bexpr → bexpr

open bexpr

def interp : bexpr → Prop
| (atom true)       => True
| (atom false)      => False
| (bexpr.and a b)   => interp a ∧ interp b
| (bexpr.or a b)    => interp a ∨ interp b
| (imp a b)         => interp a → interp b
| (bexpr.not b)     => ¬ interp b

def normalize : bexpr → Bool
| (atom b)          => b
| (bexpr.and a b)   => normalize a && normalize b
| (bexpr.or a b)    => normalize a || normalize b
| (imp a b)         => (! (normalize a)) || normalize b
| (bexpr.not b)     => ! (normalize b)

theorem normalize_correct (b : bexpr) : normalize b = true ↔ interp b := by
  induction b with
  | atom a          => cases' a <;> simp [normalize, interp]
  | and a b iha ihb => simp [normalize, interp, *]
  | or a b iha ihb  => simp [normalize, interp, *]
  | imp a b iha ihb =>
    simp [normalize, interp, ←iha, ←ihb]
    rw [Bool.eq_false_iff]
    tauto
  | not b ih        =>
    simp [normalize, interp]
    rw [Bool.eq_false_iff]
    tauto
  done


open Lean Meta Elab Tactic Qq

partial def bexprOfExpr (e : Q(Prop)) : MetaM Expr :=
match e with
| ~q(True)              => mkAppM `bexpr.atom #[mkConst ``true]
| ~q(False)             => mkAppM `bexpr.atom #[mkConst ``false]
| ~q($a ∧ $b)           => do
  let a' ← bexprOfExpr a
  let b' ← bexprOfExpr b
  mkAppM `bexpr.and #[a', b']
| ~q($a ∨ $b)           => do
  let a' ← bexprOfExpr a
  let b' ← bexprOfExpr b
  mkAppM `bexpr.or #[a', b']
| Expr.forallE _ a b _  => do
  let a' ← bexprOfExpr a
  let b' ← bexprOfExpr b
  mkAppM `bexpr.imp #[a', b']
| ~q(¬ $a)              => do
  let a' ← bexprOfExpr a
  mkAppM `bexpr.not #[a']
| _                     => failure

def changeGoal : TacticM Unit :=
  withMainContext do
    let t ← getMainTarget
    let t' : Q(bexpr) ← bexprOfExpr t
    let gl ← getMainGoal
    let gls ← gl.apply q(Iff.mp (normalize_correct $t'))
    setGoals gls

elab "change_goal" : tactic => changeGoal

example : (True → True) ∨ False := by
  change_goal
  rfl

/-!
You could imagine dooing the same with, say a SAT solver.

Modify `bexpr` to cover all propositional formulas: `atom: ℕ → bexpr`,
Add an argument to `interp`: `dict : ℕ → Prop` assigning atoms to propositions.
`normalize` becomes `is_tautology : bexpr → bool`.
`normalize_correct` becomes
 `is_tautoligy_correct (b : bexpr) : is_tautology b = tt ↔ ∀ dict, interp dict b`
`bexpr_of_bexpr` will also have to return a dictionary.

-/

/-!

# Linear arithmetic

We've used the tactic `linarith` to prove statments that follow from linear
(in)equalities in the local context.

For convenience we will work over a linear ordered ring, although this makes sense
with weaker assumptions.

An expression is *linear* in variables `x₁ ... xₙ` if it is a polynomial of degree
at most one: that is, it is a sum of products `cᵢ * xᵢ`, where each `cᵢ` is a
coefficient.

The key point: variables are not multiplied together.
`5*x + 3*y` is linear, but `5*x*y` is not.

An (in)equality is linear if it is of the form `a ⋈ b` where
⋈ is <, ≤, =, ≥ or >, and a and b are linear expressions.

-/

example (ε : ℚ) (h1 : ε > 0) : ε / 2 + ε / 3 + ε / 7 < ε :=
  by linarith

example (g v V c h : ℚ) (_h1 : h = 0) (h2 : v = V) (_h3 : V > 0) (_h4 : g > 0) (_h5 : 0 ≤ c) (_h6 : c < 1) :
  v ≤ V :=
  by linarith

example (N n : ℕ) (A l : ℚ) (_Hirrelevant : n > N) (h : A - l ≤ -(A - l)) (_h_1 : ¬A ≤ -A) (_h_2 : ¬l ≤ -l) (_h_3 : -(A - l) < 1) :
  A < l + 1 :=
  by linarith























def myStupidTactic : TacticM Unit :=
  withMainContext do
    let target ← getMainTarget
    logInfo m!"You still need to show {target} :)"
    return ()

elab "my_stupid_tactic" : tactic => myStupidTactic

example {A B : Prop} {a : A} {b : B} : A ∧ B := by
  constructor
  exact a
  exact b
  done
