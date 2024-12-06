-- To Illustrate we will build a tactic that reverses a list of goals
import Lean

open Lean Meta Elab Tactic

elab "reverse_goals" : tactic =>
  withMainContext do
    let goals : List MVarId ← getGoals
    setGoals $ List.reverse goals

elab "list_goals" : tactic =>
  withMainContext do
    let goals : List MVarId ← getGoals
    let types ← goals.mapM (λ e => e.getTag)
    dbg_trace f!"goals : {types}"

theorem test_reverse_goals : (1 = 2 ∧ 3 = 4) ∧ 5 = 6 := by
  constructor
  constructor
  list_goals
  reverse_goals
  list_goals
  repeat admit
