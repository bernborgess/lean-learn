import Lean

open Lean Expr Meta Elab Tactic

def myApply (goal : MVarId) (e : Expr) : MetaM (List MVarId) := do
  goal.checkNotAssigned `myApply
  goal.withContext do
    let target ← goal.getType
    let type ← inferType e
    let (args, _, conclusion) ← forallMetaTelescopeReducing type
    if ← isDefEq target conclusion then
      goal.assign (mkAppN e args)
      let newGoals ← args.filterMapM λ mvar => do
        let mvarId := mvar.mvarId!
        if ! (← mvarId.isAssigned) && ! (← mvarId.isDelayedAssigned) then
          return some mvarId
        else
          return none
      return newGoals.toList
    else
      throwTacticEx `myApply goal m!"{e} is not applicable to goal with target {target}"

elab "myApply" e:term : tactic => do
  let e ← Elab.Term.elabTerm e none
  Elab.Tactic.liftMetaTactic (myApply · e)

example (h : α → β) (a : α) : β := by
  myApply h
  myApply a
