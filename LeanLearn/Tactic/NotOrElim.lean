import Lean

open Lean Elab Tactic Expr Meta

/- --------------- Util.lean ---------------------------- -/
def getNatLit? : Expr → Option Nat
| app (app _ (lit (Literal.natVal x))) _ => some x
| _ => none

def stxToNat (h : Term) : TacticM Nat := do
  let expr ← elabTerm h.raw none
  match getNatLit? expr with
  | some i => pure i
  | none => throwError "getNatLit? failed"

-- Negates an expression.
-- Takes a Not out or if exists, puts one in otherwise.
def notExpr : Expr → Expr
| app (const ``Not ..) e => e
| e => mkApp (mkConst ``Not) e

-- TODO: Understand this.
def collectPropsInOrChain : Expr → MetaM (List Expr)
| app (app (const ``Or ..) e₁) e₂ => (e₁ :: ·) <$> collectPropsInOrChain e₂
| e => pure [e]

def createOrChain : List Expr → MetaM Expr
| [] => throwError "createOrChain with empty list"
| [h] => pure h
| h::t => app (app (mkConst ``Or) h) <$> createOrChain t

def collectPropsInOrChain' : Nat → Expr → MetaM (List Expr)
| l, e => do
  let li ← collectPropsInOrChain e
  let pref := List.take l li
  let suff := List.drop l li
  let suffE ← createOrChain suff
  pure $ pref ++ [suffE]

def getLength : Expr → (i : Option Nat := none) → MetaM Nat
| e, some i => do
  let li ← collectPropsInOrChain' i e
  pure $ li.length
| e, none => do
  let li ← collectPropsInOrChain e
  pure $ li.length

/- --------------- Boolean.lean ------------------------- -/


def notOrElimMeta (mvar : MVarId) (val : Expr) (i : Nat) (name : Name) : MetaM MVarId :=
  mvar.withContext do
    let type ← inferType val                  -- get the type
    let orChain := notExpr type               -- negate the chain
    let props ← collectPropsInOrChain orChain -- transform "Or chain" to list of types
    let prop := props.get! i                  -- index specific type

    withLocalDeclD (← mkFreshId) prop $ fun bv => do
      logInfo (repr bv)
      let pf : Expr ← match (← getLength orChain) == i + 1 with
        | true => pure bv
        | false =>
          let rest ← createOrChain (props.drop (i+1))
          mkAppOptM ``Or.inl #[none, rest, bv]

      let pf ← getProof i 0 props pf
      let pf := mkApp val pf
      let pf ← mkLambdaFVars #[bv] pf
      let (_,mvar') ← MVarId.intro1P $ ← mvar.assert name (notExpr prop) pf
      return mvar'

where
  getProof (i j : Nat) (props : List Expr) (val : Expr) : MetaM Expr :=
    match i with
    | 0 => pure val
    | i + 1 => do
      let currProp := props.get! j
      mkAppOptM ``Or.inr #[currProp, none, ← getProof i (j + 1) props val]


syntax (name := notOrElim) "notOrElim" term "," term : tactic
@[tactic notOrElim] def evalNotOrElim : Tactic := fun stx => do
  withMainContext do
    let i ← stxToNat ⟨stx[3]⟩
    let val ← elabTerm stx[1] none
    let fname ← mkFreshId
    let mvar ← getMainGoal
    let mvar' ← notOrElimMeta mvar val i fname
    replaceMainGoal [mvar']
    evalTactic (← `(tactic| exact $(mkIdent fname)))

/- --------------- Test/NotOrElim.lean ------------------ -/
example : ¬ (A ∨ B ∨ C ∨ D) → ¬ C := by
  intro h
  notOrElim h,2
