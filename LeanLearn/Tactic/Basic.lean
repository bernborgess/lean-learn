import Lean

open Lean Elab Tactic Meta

-- Define new lean construction
-- https://github.com/leanprover-community/lean4-metaprogramming-book/blob/master/md/main/05_syntax.md
syntax (name:=resolve) "resolve" : tactic -- no params

-- Define a property
@[tactic resolve]
-- Define a function
def evalResolve : Tactic := λ _ : Syntax => do -- function Syntax → TacticM ()
  -- s = ["resolve"]
  -- Retrieve goal
  let goal ← getMainTarget

  -- Retrieve context
  withMainContext do
    let ctx ← getLCtx
    -- Iterate on local variables
    for (v:LocalDecl) in ctx do
      -- Check if some hypothesis proves goal already
      -- logInfo m!"name: {v.userName}"
      -- logInfo m!"type: {v.type}"
      -- logInfo m!"toExpr: {repr v.toExpr}"

      let eq ← Meta.isDefEq v.type goal
      if eq then do
        -- Closes goal
        closeMainGoal v.toExpr

example (hp : p) : p := by
  resolve

example (x y z w : Nat) (h₁ : x = y) (h₂ : y = z) (h₃ : z = w) : x = w := by
  apply Eq.trans h₁
  apply Eq.trans h₂
  resolve -- applied h₃



def traceConstWithTransparency (md : TransparencyMode) (c : Name) :
    MetaM Format := do
  ppExpr (← withTransparency md $ reduce (.const c []))

@[irreducible] def irreducibleDef : Nat   := 1
def                defaultDef     : Nat   := irreducibleDef + 1
abbrev             reducibleDef   : Nat   := defaultDef + 1


#eval traceConstWithTransparency .reducible ``reducibleDef
-- defaultDef + 1
