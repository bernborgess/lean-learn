import Lean
-- Exploring TacticM

open Lean Elab Tactic

-- The simplest tactic: sorry
elab "custom_sorry_0" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    -- let goalDecl ← goal.getDecl
    -- let goalType := goalDecl.type
    -- dbg_trace f!"goal type: {goalType}"
    Lean.Elab.admitGoal goal

example : 1 = 2 := by
  custom_sorry_0
