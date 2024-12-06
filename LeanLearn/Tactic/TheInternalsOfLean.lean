import Lean
import Std

open Lean Elab Tactic Meta Expr

elab "my_assumption" : tactic => do
    let target ← getMainTarget

    for ldecl in ← getLCtx do
        if ldecl.isImplementationDetail then continue

        if ← isDefEq ldecl.type target then
            closeMainGoal ldecl.toExpr
            return

    throwTacticEx `my_assumption (← getMainGoal)
        m!"no matching hypothesis of type {indentExpr target}"

example (h : A) (_ : B) : A := by
    my_assumption

def assumpMeta (mvar : MVarId) (name : Name) : MetaM MVarId :=
    mvar.withContext do
        let target ← mvar.getType

        for ldecl in ← getLCtx do
            if ldecl.isImplementationDetail then continue

            if ← isDefEq ldecl.type target then
                let mvarId ← mvar.assert name target ldecl.toExpr
                let (_,mvar') ← MVarId.intro1P mvarId
                return mvar'

        return mvar

syntax (name := assump) "assump" : tactic
@[tactic assump] def evalAssump : Tactic := fun _ => do
    withMainContext do
        let mvar ← getMainGoal
        let fname ← mkFreshId
        let mvar' ← assumpMeta mvar fname
        replaceMainGoal [mvar']
        evalTactic (← `(tactic| exact $(mkIdent fname)))

example (h : A) (_ : A) : A := by
    assump

def assump2Meta (mvar : MVarId) : MetaM Unit :=
    mvar.withContext do
        let target ← mvar.getType

        for ldecl in ← getLCtx do
            if ldecl.isImplementationDetail then continue

            if ← isDefEq ldecl.type target then
                mvar.assignIfDefeq ldecl.toExpr
                return

syntax (name := assump2) "assump2" : tactic
@[tactic assump2] def evalAssump2 : Tactic := fun _ => do
    withMainContext do
        let mvar ← getMainGoal
        assump2Meta mvar

example (h : A) (_ : B) (_ : A) (_ : A): A := by
    assump2
