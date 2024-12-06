import Lean
-- The custom_assump tactic: Accessing Hypotheses

elab "get_goal_type" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let goalType ← Lean.Elab.Tactic.getMainTarget
    dbg_trace f!"goal type: {goalType}"

-- Access the list of hypotheses
elab "list_local_declarations" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let ctx ← Lean.MonadLCtx.getLCtx
    ctx.forM fun decl : Lean.LocalDecl => do
      let declExpr := decl.toExpr
      let declName := decl.userName
      dbg_trace f!"+ local decl: name: {declName} | expr: {declExpr}"


-- Get the type of LocalDecl by calling `Lean.Meta.inferType`
elab "list_local_declarations_2" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let ctx ← Lean.MonadLCtx.getLCtx
    ctx.forM fun decl : Lean.LocalDecl => do
      let declExpr := decl.toExpr
      let declName := decl.userName
      let declType ← Lean.Meta.inferType declExpr -- FIND THE TYPE
      dbg_trace f!"+ local decl: name: {declName} | expr: {declExpr} | type: {declType}"

-- Now we can check if the TYPE of LocalDecl is equal to the goal type
-- with Lean.Meta.isExprDefEq
elab "list_local_declarations_3" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let goalType ← Lean.Elab.Tactic.getMainTarget -- GOAL TYPE
    let ctx ← Lean.MonadLCtx.getLCtx -- LOCAL CTX
    ctx.forM fun decl : Lean.LocalDecl => do
      let declExpr := decl.toExpr -- Expr of declaration
      let declName := decl.userName
      let declType ← Lean.Meta.inferType declExpr -- THE TYPE
      let eq? ← Lean.Meta.isExprDefEq declType goalType -- CHECK TYPES ARE EQUAL
      dbg_trace f!"+ local decl[EQUAL? {eq?}]: name: {declName}"

-- A TRUE was found, we can match the expressions
--  then we can close the goal.

elab "custom_assump" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let goalType ← Lean.Elab.Tactic.getMainTarget

    let ctx ← Lean.MonadLCtx.getLCtx
    let option_matching_expr ← ctx.findDeclM? fun ldecl : Lean.LocalDecl => do
      let declExpr := ldecl.toExpr
      let declType ← Lean.Meta.inferType declExpr
      if (← Lean.Meta.isExprDefEq declType goalType)
        then return some declExpr
        else return none

    match option_matching_expr with
    | some e => Lean.Elab.Tactic.closeMainGoal e
    | none => do
      let goal ← Lean.Elab.Tactic.getMainGoal
      Lean.Meta.throwTacticEx `custom_assump goal
        (m!"unable to find matching hypothesis of type ({goalType})")

theorem assump_correct (H1 : 1 = 1) (H2 : 2 = 2) : 2 = 2 := by
  custom_assump

theorem assump_wrong (H1 : 1 = 1) : 2 = 2 := by
  sorry
  -- custom_assump
-- tactic 'custom_assump' failed,
-- unable to find matching hypothesis of type (2 = 2)

-- ? TERSE WORLD
open Lean Elab Tactic MonadLCtx Meta

elab "assumpy" : tactic =>
  withMainContext do
    let goalType ← getMainTarget

    -- Maybe find a matching expression in local context
    let option_matching_expr ← (← getLCtx).findDeclM?
      fun ld : LocalDecl => do
        -- Retrieve type from ld
        let declType ← inferType ld.toExpr

        -- Check equalifty of types
        if (← isExprDefEq declType goalType)
          then return some ld.toExpr
          else return none

    match option_matching_expr with
    | some e => closeMainGoal e
    | none => do
      let goal ← getMainGoal
      throwTacticEx `custom_assump goal
        (m!"unable to find matching hypothesis of type ({goalType})")


example (h1 : 1 = 2) : 1 = 2 := by
  assumpy

def multiple_checks (i : Int) : Option Nat := do
  guard (i > 0)
  guard (i % 2 == 1)
  let n := i.toNat
  pure $ n + n

#eval multiple_checks (-1)
