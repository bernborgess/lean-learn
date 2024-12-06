import Lean

open Lean Elab Tactic Meta Expr

-- Syntactic definition > andElim h, 1
syntax (name := andElim) "andElim" term "," term : tactic

-- Helper to convert Expr to Nat
def getNatLit? : Expr -> Option Nat
  | app (app _ (lit (Literal.natVal x))) _ => some x
  | _ => none

-- Helper to convert Term to a Nat
def stxToNat (h : Term) : TacticM Nat := do
  let expr ← elabTerm h.raw none
  match getNatLit? expr with
  | some i => pure i
  | none   => throwError "getNatLit? failed."

-- Iterates Expr and returns first Name of tree
def getFirstBinderName : Expr → MetaM Name
  | app e _ => getFirstBinderName e
  | const nm .. => pure nm
  | _ => throwError "getFirstBinderName failed."

-- Retrieves number of clauses in And tree
def getLengthAnd : Expr → Nat
  | app (app (const ``And ..) _) e2 => 1 + getLengthAnd e2
  | _ => 1

-- Helper (tail)
def getProof (i : Nat) (hyp : Expr) : MetaM Expr :=
  match i with
  | 0 => pure hyp
  | (i + 1) => do
    let rc ← getProof i hyp
    mkAppM ``And.right #[rc] -- Tail operation

-- Helper unwrap lambda
def recGetLamBody (e : Expr) : Expr :=
  match e with
  | lam _ _ b _ => recGetLamBody b
  | e => e

-- Meta version of andElim
def andElimMeta (mvar : MVarId) (val : Expr) (i : Nat) (name : Name) : MetaM MVarId :=
  mvar.withContext do
    let andLength := getLengthAnd (← inferType val)
    let rudder ← getProof i val
    let answer ← if i < andLength - 1
                  then mkAppM ``And.left #[rudder]
                  else pure rudder

    let goal ← inferType answer
    let asserted ← mvar.assert name goal answer
    let (_,mvar') ← MVarId.intro1P asserted
    return mvar'

@[tactic andElim]
def evalAndElim : Tactic := fun stx =>
  withMainContext do
    let mvar ← getMainGoal          -- TacticM MVarId

    let val ← elabTerm stx[1] none  -- Syntax → Option Expr → TacticM Expr

    let idx : Term := ⟨stx[3]⟩  -- Syntax → Term
    let i ← stxToNat idx       -- Term → TacticM Nat

    let fname ← mkFreshId -- TacticM Name
    let tact ← `(tactic| exact $(mkIdent fname)) -- ?

    let mvar' ← andElimMeta mvar val i fname

    replaceMainGoal [mvar']

    -- ????
    -- evalTactic (← `(tactic| exact $(mkIdent fname)))

    evalTactic tact

def constant (x:α)  (_:β) := x

example : A ∧ B ∧ C → B := by
  intro h
  andElim h, 1



def jn (x:α) (r: Nat → Option α) (k:Nat): Option α :=
  match k with
  | 0 => some x
  | _ => r (k - 1)

-- (a -> b -> b) -> b -> [a] -> b

def exprSubscript (val:List α) (i:Nat) : Option α :=
  val.foldr jn (constant none) i

-- exprSubscript []
def s := exprSubscript [1,2,3] 1
-- #print s
-- #eval s


def neverNegative (i:Int) : Option Nat := do
  guard (i >= 0)
  i.toNat

def k := [1,2,3].length

/-
.app
  (.app
    (.const `And [])
    (.fvar (Lean.Name.mkNum `_uniq 17301))
  )
  (.app
    (.app
      (.const `And [])
      (.fvar (Lean.Name.mkNum `_uniq 17302)
    ))
  (.fvar (Lean.Name.mkNum `_uniq 17303)))




Lean.Expr.app
  (Lean.Expr.app
    (Lean.Expr.const `And [])
    (Lean.Expr.fvar (Lean.Name.mkNum `_uniq 17301)))
  (Lean.Expr.app
    (Lean.Expr.app
      (Lean.Expr.const `And [])
      (Lean.Expr.fvar (Lean.Name.mkNum `_uniq 17302)))
    (Lean.Expr.fvar (Lean.Name.mkNum `_uniq 17303)))
-/
