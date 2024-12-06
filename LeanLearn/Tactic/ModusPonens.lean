import Lean
import Qq
open Lean Elab Tactic Qq

elab "modus_ponens" : tactic => do
    for ldecl in ← getLCtx do
        if let some goalType ← checkTypeQ (u := levelOne) ldecl.type q(Prop) then
        if let ~q((((($a : Prop)) → $b) : Prop)) := goalType then
            let name := mkIdent ldecl.userName
            evalTactic (← `(tactic| apply $name ; assumption ))

syntax (name := modusPonens) "modus_ponens" : tactic

@[tactic modusPonens]
def evalModusPonens : Tactic := λ _ =>
    for ldecl in ← getLCtx do
        if let some goalType ← checkTypeQ (u := levelOne) ldecl.type q(Prop) then
        if let ~q((((($a : Prop)) → $b) : Prop)) := goalType then
            logInfo m!"Got a "
            let name := mkIdent ldecl.userName
            evalTactic (← `(tactic| apply $name ; assumption ))

example {A B : Prop} (P : A → B) (a : A) : B := by
    modus_ponens
