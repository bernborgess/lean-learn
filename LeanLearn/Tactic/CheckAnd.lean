import Lean
import Qq

open Lean Elab Tactic Qq

elab "check_and" : tactic => do
    for ldecl in ← getLCtx do
        if let some goalType ← checkTypeQ (u := levelOne) ldecl.type q(Prop) then
        if let ~q((And $A $B)) := goalType then
            let name := mkIdent ldecl.userName
            logInfo name
            -- evalTactic (← `(tactic| apply $name ; assumption ))


example {A B : Prop} (P : A ∧ B) : A := by
  check_and
  sorry
