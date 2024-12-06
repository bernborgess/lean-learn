import Lean
import Std.Data.List.Basic
import TacticExample.CS1951x.Lectures.L16_MonadsTactics

open Lean Lean.Meta Lean.Elab.Tactic Lean.TSyntax

/-! ## Expressions

The metaprogramming framework revolves around the type `Expr` of expressions or
terms. -/

#print Expr

/-! ### Names

We can create literal names with backticks:

* Names with a singgle backtick, `n, are not checked for existence.

* Names with two backticks, ``n, are resolved and checked.

-/

namespace NameSpace

def k := 1

#check `x
#eval `x
#eval `k
#eval `NameSpace.k -- suboptimal
#eval ``k
-- #eval ``idk -- fails

end NameSpace


/- ### Constants -/

#check Expr.const
-- Name → List Level → Expr

#eval ppExpr (Expr.const ``Nat.add [])
#eval ppExpr (Expr.const ``Nat [])


/- ### Sorts (lecture 12) -/

#check Expr.sort

#eval ppExpr (Expr.sort Level.zero)
#eval ppExpr (Expr.sort (Level.succ Level.zero))

/- ### Free Variables -/

#check Expr.fvar

#check FVarId.mk "n"
#eval ppExpr (Expr.fvar (FVarId.mk "n"))

/- ### Metavariables -/

#check Expr.mvar
-- placeholder for a goal, with a mvarid

/- ### Applications -/

#check Expr.app
-- We can apply some expression to another
#eval ppExpr (Expr.app (Expr.const ``Nat.succ []) (Expr.const ``Nat.zero []))

/- ### Anonymous Functions and Bound Variables -/

#check Expr.bvar
#check Expr.lam

#eval ppExpr (Expr.bvar 0)

#eval ppExpr (Expr.lam `x (Expr.const ``Nat []) (Expr.bvar 0) BinderInfo.default)

#eval ppExpr (.lam `x (.const ``Nat []) (.lam `y (.const ``Nat []) (.bvar 1) .default) .default)

/- ### Dependent Function Types -/
#check Expr.forallE

#eval ppExpr (Expr.forallE `n (Expr.const ``Nat []) (Expr.app (Expr.const ``Even []) (Expr.bvar 0)) BinderInfo.default)

#eval ppExpr (Expr.forallE `dummy (Expr.const `Nat []) (Expr.const `Bool []) BinderInfo.default)


/-! ## Second Example: A Conjuction-Destrucring Tactic

We define a `destruct_and` tactic that automates the elimination of `∧` in
premises, automating proofs such as these: -/

theorem abc_a (a b c : Prop) (h : a ∧ b ∧ c) :
  a :=
  And.left h

theorem abc_b (a b c : Prop) (h : a ∧ b ∧ c) :
  b :=
  And.left (And.right h)

theorem abc_bc (a b c : Prop) (h : a ∧ b ∧ c) :
  b ∧ c :=
  And.right h

theorem abc_c (a b c : Prop) (h : a ∧ b ∧ c) :
  c :=
  And.right (And.right h)

/- Our tactic relies on a helper function, which takes as argument the
hypothesis `h` to use as an expression: -/

partial def destructAndExpr (hP : Expr) : TacticM Bool :=
  withMainContext do
    let target ← getMainTarget

    -- Check if P is the conjuction we need
    let P ← inferType hP
    let eq ← isDefEq P target
    if eq then
      let goal ← getMainGoal
      goal.assign hP
      return true

    -- Check if P is a conjuction at all
    match Expr.and? P with
    | .none         => return false
    | .some (_Q, _R)  =>

      -- Check if goal is inside Q
      let hQ ← mkAppM ``And.left #[hP] -- this can fail
      let success ← destructAndExpr hQ
      if success then
        return true

      -- Check if goal is inside R
      let hR ← mkAppM ``And.right #[hP] -- todo: Try quoting ```(And.right %%hP)
      destructAndExpr hR

#check Expr.and?

def destructAnd (name : Name) : TacticM Unit :=
  withMainContext do
    let h ← getFVarFromUserName name
    let success ← destructAndExpr h
    if ! success then
      failure

elab "destruct_and" h:ident : tactic => destructAnd (getId h)

/- Let us check that our tactic works: -/

theorem abc_a₂ (a b c : Prop) (h : a ∧ b ∧ c) :
  a := by
  destruct_and h
  done

theorem abc_b₂ (a b c : Prop) (h : a ∧ b ∧ c) :
  b := by
  destruct_and h
  done

theorem abc_bc₂ (a b c : Prop) (h : a ∧ b ∧ c) :
  b ∧ c := by
  destruct_and h
  done

theorem abc_c₂ (a b c : Prop) (h : a ∧ b ∧ c) :
  c := by
  destruct_and h
  done

-- a ∧ b is not a subexpression of a ∧ (b ∧ c)

theorem abc_ab (a b c : Prop) (h : a ∧ b ∧ c) :
  a ∧ b := by
  -- destruct_and h -- fails
  have ⟨ha,hb,_⟩ := h
  constructor
  repeat assumption
  done

/-! ### Third Example: A Direct Proof Finder

Finally, we implement a `prove_direct` tool that traverses all theorems in the
database and checks whether one of them can be used to prove the current
goal.  -/

def isTheorem : ConstantInfo → Bool
| .axiomInfo _  => true
| .thmInfo _    => true
| _             => false

def applyConstant (name : Name) : TacticM Unit := do
  let cst ← mkConstWithFreshMVarLevels name
  liftMetaTactic (·.apply cst)

def andThenOnSubgoals (tac₁ tac₂ : TacticM Unit) : TacticM Unit := do
  let origGoals ← getGoals
  let mainGoal ← getMainGoal
  setGoals [mainGoal]
  tac₁
  let subgoals₁ ← getUnsolvedGoals
  let mut newGoals := []
  for subgoal in subgoals₁ do
    let isAssigned ← subgoal.isAssigned
    if ! isAssigned then
      setGoals [subgoal]
      tac₂
      let subgoals₂ ← getUnsolvedGoals
      newGoals := newGoals ++ subgoals₂
  setGoals (newGoals ++ origGoals.tail)

def proveUsingTheorem (name : Name) : TacticM Unit :=
  andThenOnSubgoals (applyConstant name) hypothesis

def proveDirect : TacticM Unit := do
  let origGoals ← getUnsolvedGoals
  let goal ← getMainGoal
  setGoals [goal]
  let env ← getEnv
  for (name,info) in (Environment.constants env).toList do
    if ! isTheorem info then continue
    if info.isUnsafe then continue -- not partial
    try
      proveUsingTheorem name
      logInfo m!"Change me to `exact {name}`"
      setGoals (origGoals.tail)
      return
    catch _ => continue
  failure

elab "prove_direct" : tactic => proveDirect

/- Let us check that our tactic works: -/

theorem Nat.Eq_summ (x y : Nat) (h : x = y) :
  y = x := by
  -- prove_direct
  exact Eq.symm h
  done

theorem Nat.Eq_trans (x y z : Nat) (hxy : x = y) (hyz : y = z) :
  x = z := by
  prove_direct
  done

/- Lean has `library_search`: -/

theorem List.reverse_twice_library_search (xs : List Nat) :
  List.reverse (List.reverse xs) = xs := by
  -- library_search -- not working LOL
  -- prove_direct
  exact List.reverse_reverse xs
  done
