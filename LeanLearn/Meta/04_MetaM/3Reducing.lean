import Lean

open Lean Meta Expr Eval

def traceConstWithTransparency (md : TransparencyMode) (c : Name) : MetaM Format := do
  ppExpr (← withTransparency md $ reduce (.const c []))

@[irreducible] def  irreducibleDef  : Nat   := 1
def                 defaultDef      : Nat   := irreducibleDef + 2
abbrev              reducibleDef    : Nat   := defaultDef + 3

#eval traceConstWithTransparency .reducible ``reducibleDef
#eval traceConstWithTransparency .instances ``reducibleDef
#eval traceConstWithTransparency .default ``reducibleDef
#eval traceConstWithTransparency .all ``reducibleDef

-- Let lean print implicit arguments
-- set_option pp.explicit true
#eval traceConstWithTransparency .reducible ``reducibleDef
-- @HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) defaultDef 3

#eval traceConstWithTransparency .all ``reducibleDef
-- 3

open Lean.Elab.Term in
def whnf' (e : TermElabM Syntax) : TermElabM Format := do
  let e ← elabTermAndSynthesize (← e) none
  ppExpr (← whnf e)

#eval whnf' `(List.cons 1 [])
-- [1]

#eval whnf' `(List.cons (1 + 1) [])
-- [1 + 1]

#eval withTransparency .reducible $ whnf' `(List.append [1] [2])
-- List.append [1] [2]

#eval whnf' `(λ x : Nat => x)
-- fun x => x

#eval whnf' `(∀ x, x > 0)
-- ∀ (x : Nat), x > 0

#eval whnf' `(Type 3)
-- Type 3

#eval whnf' `((15 : Nat))
-- 15

#eval whnf' `(List.append [1])
-- fun x => 1 :: List.append [] x


#eval whnf' `((λ x y : Nat => x + y) 1)
-- fun y => 1 + y

#eval whnf' `(let x : Nat := 1; x)
-- 1


def matchAndReducing (e : Expr) : MetaM (Option (Expr × Expr)) := do
  match ← whnf e with
  | (.app (.app (.const ``And _) P) Q) => return some (P, Q)
  | _ => return none

def matchAndReducing₂ (e : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  match ← whnf e with
  | (.app (.app (.const ``And _) P) e') =>
    match ← whnf e' with
    | (.app (.app (.const ``And _) Q) R) => return some (P, Q, R)
    | _ => return none
  | _ => return none

-- Without MetaM inference
def appendAppendRHSExpr₁ (u : Level) (α xs ys : Expr) : Expr :=
  mkAppN (.const ``List.append [u])
    #[α, mkAppN (.const ``List.append [u]) #[α, xs, ys], xs]

-- With MetaM inference
def appendAppendRHSExpr₂ (xs ys : Expr) : MetaM Expr := do
  mkAppM ``List.append #[← mkAppM ``List.append #[xs, ys], xs]


-- Direct lambda
def doubleExpr₁ : Expr :=
  .lam `x (.const ``Nat []) (mkAppN (.const ``Nat.add []) #[.bvar 0, .bvar 0])
    BinderInfo.default

-- Using mkAppM
def doubleExpr₂ : MetaM Expr :=
  withLocalDecl `x BinderInfo.default (.const ``Nat []) λ x => do
    let body ← mkAppM ``Nat.add #[x, x]
    mkLambdaFVars #[x] body

#eval show MetaM _ from do
  ppExpr (← doubleExpr₂)

-- fun x => Nat.add x x

#eval ppExpr doubleExpr₁
-- fun x => Nat.add x x
