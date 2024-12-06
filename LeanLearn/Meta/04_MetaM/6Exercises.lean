import Lean

open Lean Meta Expr Elab Term

-- 1. [Metavariables] Create a metavariable with type Nat, and assign to it value 3.
-- Notice that changing the type of the metavariable from Nat to, for example, String,
-- doesn't raise any errors - that's why, as was mentioned, we must make sure
-- `(a) that val must have the target type of mvarId and`
-- `(b) that val must only contain fvars from the local context of mvarId`.

def nat := Expr.const ``Nat []
def string := Expr.const ``String []

#eval show MetaM Unit from do
  let mvar1 ← mkFreshExprMVar nat (userName := `mvar1)
  IO.println s!"{← instantiateMVars mvar1} ← mvar1"

  mvar1.mvarId!.assign (mkNatLit 3)
  IO.println s!"{← instantiateMVars mvar1} ← mvar1"

-- def exercise1 : MetaM Unit := do
--   let mvar1 ← mkFreshExprMVar nat (userName := `mvar1)
  -- mvar1.mvarId!.assign (mkNatLit 3)

-- 2. [Metavariables] What would
-- instantiateMVars (Lean.mkAppN (Expr.const 'Nat.add []) #[mkNatLit 1, mkNatLit 2])
-- output?

def add := Expr.const ``Nat.add []

def onePlusTwo:= (Lean.mkAppN add #[mkNatLit 1, mkNatLit 2])

def exercise2 : MetaM Expr := instantiateMVars onePlusTwo

#eval show MetaM Unit from do
  let expr ← exercise2
  IO.println expr

-- ? Outputs the same expression, there are no metavariables

-- 3. [Metavariables] Fill in the missing lines in the following code.

def bid := BinderInfo.default

-- λ x . λ y . λ z . x + y + z
def add3 : Expr :=
  .lam `x nat (
  .lam `y nat (
  .lam `z nat (
    mkAppN add #[ .bvar 2, mkAppN add #[.bvar 1, .bvar 0]]
  ) bid ) bid ) bid

#eval add3
-- elab "add3" : term => return add3
-- #check add3


#eval show MetaM Unit from do
  -- (λ x -> x + 1) (0)
  let oneExpr := Expr.app (Expr.const `Nat.succ []) (Expr.const ``Nat.zero [])
  -- (λ x -> x + 1) ((λ x -> x + 1) (0))
  let twoExpr := Expr.app (Expr.const `Nat.succ []) oneExpr

  -- Create `mvar1` with type `Nat`
  let mvar1 ← mkFreshExprMVar nat (userName := `mvar1)

  -- Create `mvar2` with type `Nat`
  let mvar2 ← mkFreshExprMVar nat (userName := `mvar2)

  -- Create `mvar3` with type `Nat`
  let mvar3 ← mkFreshExprMVar nat (userName := `mvar3)

  -- Assign `mvar1` to `2 + ?mvar2 + ?mvar3`
  mvar1.mvarId!.assign (mkAppN add3 #[twoExpr, mvar2, mvar3])
  -- mvar1.mvarId!.assign (mkAppN add #[mkAppN add #[twoExpr, mvar2], mvar3])
  -- mvar1.mvarId!.assign (mkAppN add #[mkAppN add #[mkNatLit 2, mvar2], mvar3])

  -- Assign `mvar3` to `1`
  mvar3.mvarId!.assign (mkNatLit 1)

  -- Instantiate `mvar1`, which should result in expression `2 + ?mvar2 + 1`
  IO.println s!"{← instantiateMVars mvar1} ← mvar1"

-- 4. [Metavariables] Consider the theorem red, and tactic explore below.
-- a) What would be the type and userName of metavariable mvarId?
-- b) What would be the types and userNames of all local declarations in
-- this metavariable's local context? Print them all out.
elab "explore" : tactic => do
  let mvarId : MVarId ← Lean.Elab.Tactic.getMainGoal
  let metavarDecl : MetavarDecl ← mvarId.getDecl

  IO.println "Our metavariable"
  IO.println s!"{metavarDecl.userName} : {metavarDecl.type}"

  IO.println "All of its local declarations"
  let localContext := metavarDecl.lctx
  for localDecl in localContext do
    if localDecl.isImplementationDetail then
      IO.println s!"\n(implementation detail) {localDecl.userName} : {localDecl.type}"
    else
      IO.println s!"\n{localDecl.userName} : {localDecl.type}"

theorem red (hA : 1 = 1) (hB : 2 = 2) : 2 = 2 := by
  explore
  sorry

-- 5.[Metavariables] Write a tactic solve that proves the theorem red.
elab "solve" : tactic => do
  let mvarId ← Lean.Elab.Tactic.getMainGoal
  let goal ← mvarId.getType

  for dcl in ← getLCtx do
    if dcl.isImplementationDetail then
      continue

    let eq ← Meta.isDefEq goal dcl.type

    if eq then do
      mvarId.assign dcl.toExpr
      break

theorem red' (hA : 1 = 1) (hB : 2 = 2) : 2 = 2 := by
  solve

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- -- -- -- -- -- -- -- -- Computation -- -- -- -- -- -- -- -- --
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --

-- 6.[Computation] What is the normal form of the following expressions:
-- * a) fun x => x of type Bool → Bool

def boool : Expr := .const ``Bool []

def booleanId : Expr := Expr.lam `x boool (
  .bvar 0
  ) BinderInfo.default

#eval reduce booleanId

-- Answer:
-- Lean.Expr.lam `x (Lean.Expr.const `Bool []) (Lean.Expr.bvar 0) (Lean.BinderInfo.default)

-- * b) (fun x => x) ((true && false) || true) of type Bool

def theTrue   : Expr := .const `Bool.true  []

def theFalse  : Expr := .const `Bool.false []

def trueAndFalse : Expr := mkAppN (.const ``and []) #[theTrue, theFalse]

def tafOrTrue : Expr := mkAppN (.const ``or []) #[trueAndFalse, theFalse]

def applyBooleanId : Expr := Expr.app booleanId tafOrTrue

-- Answer:
-- Lean.Expr.const `Bool.false []

-- * c) 800 + 2 of type Nat

def e800plus2 := mkAppN add #[mkNatLit 800, mkNatLit 2]

-- Answer:
-- Lean.Expr.lit (Lean.Literal.natVal 802)


-- 7.[Computation] Show that 1 created with Expr.lit (Lean.Literal.natVal 1)
-- is definitionally equal to an expression created with
-- Expr.app (Expr.const ``Nat.succ []) (Expr.const ``Nat.zero [])

#eval show MetaM Unit from do
  let e1 : Expr := Expr.lit (Lean.Literal.natVal 1)
  let e2 : Expr := Expr.app (Expr.const ``Nat.succ []) (Expr.const ``Nat.zero [])
  let ans ← isDefEq e1 e2
  IO.println s!"It is the same: {ans}"

-- 8.[Computation] Determine whether the following expressions are definitionally equal.
-- If Lean.Meta.isDefEq succeeds, and it leads to metavariable assignment,
-- write down the assignments.

-- * a) 5 =?= (fun x => 5) ((fun y : Nat → Nat => y) (fun z : Nat => z))

#eval show MetaM Unit from do
  -- 5
  let e1 : Expr := mkNatLit 5

  -- (fun x => 5) ((fun y : Nat → Nat => y) (fun z : Nat => z))
  let const5 : Expr := .lam `x nat (mkNatLit 5) BinderInfo.default
  let idY : Expr := .lam `y (.forallE (.mkNum `a 1) nat nat .default) (.bvar 0) .default
  let idZ : Expr := .lam `z nat (.bvar 0) .default
  let e2 : Expr := .app const5 (.app idY idZ)

  let ans ← isDefEq e1 e2
  IO.println s!"It is the same: {ans}"


-- * b) 2 + 1 =?= 1 + 2

#eval show MetaM Unit from do
  -- 2 + 1
  let e1 : Expr := mkAppN add #[mkNatLit 2, mkNatLit 1]

  -- 1 + 2
  let e2 : Expr := mkAppN add #[mkNatLit 1, mkNatLit 2]

  let ans ← isDefEq e1 e2
  IO.println s!"It is the same: {ans}"


-- * c) ?a =?= 2, where ?a has a type String

#eval show MetaM Unit from do
  -- ?a where ?a has a type String
  let e1 : Expr ← mkFreshExprMVar string (userName := `e1)

  -- 2
  let e2 : Expr := mkNatLit 2

  let ans ← isDefEq e1 e2
  IO.println s!"It is the same: {ans} "

-- * d) ?a + Int =?= "hi" + ?b, where ?a and ?b don't have a type

def int := Expr.const ``Int []

#eval show MetaM Unit from do
  let a ← mkFreshExprMVar Option.none (userName := `a)
  let b ← mkFreshExprMVar Option.none (userName := `b)

  -- ?a + Int
  let e1 := mkAppN add #[a, int]

  -- "hi" + ?b
  let e2 := mkAppN add #[mkStrLit "hi", b]

  let ans ← isDefEq e1 e2
  IO.println s!"It is the same: {ans} "

  IO.println s!"a : {← instantiateMVars a}"
  IO.println s!"b : {← instantiateMVars b}"


-- * e) 2 + ?a =?= 3

#eval show MetaM Unit from do
  let a ← mkFreshExprMVar nat (userName := `a)

  -- 2 + ?a
  let e1 := mkAppN add #[mkNatLit 2, a]

  -- 3
  let e2 := mkNatLit 3

  let ans ← isDefEq e1 e2
  IO.println s!"It is the same: {ans} "

  IO.println s!"a : {← instantiateMVars a}"


-- * f) 2 + ?a =?= 2 + 1

#eval show MetaM Unit from do
  let a ← mkFreshExprMVar nat (userName := `a)

  -- 2 + ?a
  let e1 := mkAppN add #[mkNatLit 2, a]

  -- 2 + 1
  let e2 := mkAppN add #[mkNatLit 2, mkNatLit 1]

  let ans ← isDefEq e1 e2
  IO.println s!"It is the same: {ans} "

  IO.println s!"a : {← instantiateMVars a}"

-- 9.[Computation] Write down what you expect the following code to output.
@[reducible] def reducibleDef     : Nat := 1 -- same as `abbrev`
@[instance] def instanceDef       : Nat := 2 -- same as `instance`
def defaultDef                    : Nat := 3
@[irreducible] def irreducibleDef : Nat := 4

@[reducible] def sum := [reducibleDef, instanceDef, defaultDef, irreducibleDef]

#eval show MetaM Unit from do
  let constantExpr := Expr.const `sum []

  Meta.withTransparency Meta.TransparencyMode.reducible do
    let reducedExpr ← Meta.reduce constantExpr
    dbg_trace (← ppExpr reducedExpr)  -- [1, i, d, i]

  Meta.withTransparency Meta.TransparencyMode.instances do
    let reducedExpr ← Meta.reduce constantExpr
    dbg_trace (← ppExpr reducedExpr)  -- [1, 2, d, i]

  Meta.withTransparency Meta.TransparencyMode.default do
    let reducedExpr ← Meta.reduce constantExpr
    dbg_trace (← ppExpr reducedExpr)  -- [1, 2, 3, i]

  Meta.withTransparency Meta.TransparencyMode.all do
    let reducedExpr ← Meta.reduce constantExpr
    dbg_trace (← ppExpr reducedExpr)  -- [1, 2, 3, 4]

  let reducedExpr ← Meta.reduce constantExpr
  dbg_trace (← ppExpr reducedExpr)    -- [1, 2, 3, i]

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- -- -- -- -- -- --  Constructing Expressions  -- -- -- -- -- --
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --


-- 10. [Constructing Expressions]
-- Create expression fun x, 1 + x in two ways:

-- * a) not idiomatically, with loose bound variables
def expr10_1 : MetaM Expr := do
  let body := mkAppN add #[mkNatLit 1, .bvar 0]
  return .lam `x nat body .default

#eval show MetaM _ from do
  ppExpr (← expr10_1)

-- * b) idiomatically.
def expr10_2 : MetaM Expr := do
  withLocalDecl `x .default nat λ x => do
    let body ← mkAppM `Nat.add #[mkNatLit 1, x]
    mkLambdaFVars #[x] body

#eval show MetaM _ from do
  ppExpr (← expr10_2)

-- ? In what version can you use Lean.mkAppN?
-- In both, we need to use bvars

-- ? In what version can you use Lean.Meta.mkAppM?
-- The idiomatical, under the MetaM monad, with a lambda

-- 11. [Constructing Expressions]
-- Create expression ∀ (yellow: Nat), yellow.
def expr11_1 : MetaM Expr := do
  withLocalDecl `yellow .default nat λ yellow => do
    mkForallFVars #[yellow] yellow

def expr11_2 : MetaM Expr := do
  return .forallE `yellow nat (.bvar 0) .default

#eval show MetaM _ from do
  dbg_trace (← expr11_1)

#eval show MetaM _ from do
  dbg_trace (← expr11_2)

-- 12. [Constructing Expressions]
-- Create expression ∀ (n : Nat), n = n + 1 in two ways:

def eq := Expr.const ``Eq []

-- * a) not idiomatically, with loose bound variables
def expr_12_1 : MetaM Expr := do
  let n_plus_1    := mkAppN add #[.bvar 0, mkNatLit 1]
  let body        := mkApp3 eq nat (.bvar 0) n_plus_1
  return .forallE `n nat body .default

#eval show MetaM _ from do
  ppExpr (← expr_12_1)

-- * b) idiomatically.
def expr_12_2 : MetaM Expr := do
  withLocalDecl `n  .default nat λ n => do
    let n_plus_1 ← mkAppM `Nat.add #[n, mkNatLit 1]
    let body ← mkEq n n_plus_1
    mkForallFVars #[n] body

#eval show MetaM _ from do
  ppExpr (← expr_12_2)


-- In what version can you use Lean.mkApp3?
-- both can use it, wit bvars

-- In what version can you use Lean.Meta.mkEq?
-- only the idiomatical, under the MetaM monad

-- 13.[Constructing Expressions]
-- Create expression
-- fun (f : Nat → Nat), ∀ (n : Nat), f n = f (n + 1)
-- idiomatically.

def nat_to_nat : Expr := .forallE `a nat nat .default

def expr_13 : MetaM Expr := do

  withLocalDecl `f .default nat_to_nat λ f => do

    let lb ← withLocalDecl `n .default nat λ n => do

      let fn        := .app f n
      let fn_plus_1 := .app f (mkAppN add #[n, mkNatLit 1])
      let body      := mkApp3 eq nat fn fn_plus_1

      mkForallFVars #[n] body

    mkLambdaFVars #[f] lb

#eval show MetaM _ from do
  dbg_trace nat_to_nat

#eval show MetaM _ from do
  ppExpr (← expr_13)

-- 14. [Constructing Expressions]
-- What would you expect the output of the following code to be?
#eval show TermElabM _ from do
  let stx : Syntax ← `(∀ (a : Prop) (b : Prop), a ∨ b → b → a ∧ a)
  let expr ← elabTermAndSynthesize stx none

  let (_, _, conclusion) ← forallMetaTelescope expr
  dbg_trace conclusion -- And ?_uniq.10 ?_uniq.10

  let (_, _, conclusion) ← forallMetaBoundedTelescope expr 2
  dbg_trace conclusion -- (Or ?_uniq.14 ?_uniq.15) -> ?_uniq.15 -> (And ?_uniq.14 ?_uniq.14)

  let (_, _, conclusion) ← lambdaMetaTelescope expr
  dbg_trace conclusion -- forall (a.1 : Prop) (b.1 : Prop), (Or a.1 b.1) -> b.1 -> (And a.1 a.1)

-- 15. [Backtracking]
-- Check that the expressions
-- ?a + Int and "hi" + ?b
-- are definitionally equal with isDefEq
-- (make sure to use the proper types or Option.none
-- for the types of your metavariables!).
-- Use saveState and restoreState to revert metavariable assignments.

#eval show MetaM Unit from do
  let a ← mkFreshExprMVar string (userName := `a)
  let b ← mkFreshExprMVar (Expr.sort (Nat.toLevel 1)) (userName := `b)

  -- ?a + Int
  let c := mkAppN add #[a, int]

  -- "hi" + ?b
  let d := mkAppN add #[mkStrLit "hi", b]

  IO.println s!"Value in c: {← instantiateMVars c}"
  IO.println s!"Value in d: {← instantiateMVars d}"

  let state ← saveState

  if ← isDefEq c d then
    IO.println true
    IO.println s!"Value in c: {← instantiateMVars c}"
    IO.println s!"Value in d: {← instantiateMVars d}"

  restoreState state
  IO.println "\nRestored state\n"

  IO.println s!"Value in c: {← instantiateMVars c}"
  IO.println s!"Value in d: {← instantiateMVars d}"
