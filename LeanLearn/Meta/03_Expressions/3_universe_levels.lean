import Lean
open Lean Expr Elab

def z' := const `Nat.zero []
#eval z' -- Lean.Expr.const `Nat.zero []

def z := Expr.const ``Nat.zero []
#eval z -- Lean.Expr.const `Nat.zero []

def one := Expr.app (.const ``Nat.succ []) z
#eval one -- Lean.Expr.app
--            (Lean.Expr.const `Nat.succ [])
--            (Lean.Expr.const `Nat.zero [])

def natExpr: Nat → Expr
| 0     => z
| n + 1 => .app (.const ``Nat.succ []) (natExpr n)

def sumExpr : Nat → Nat → Expr
| n, m => mkAppN (.const ``Nat.add []) #[natExpr n, natExpr m]

def constZero : Expr :=
  .lam `x (.const ``Nat []) (.const ``Nat.zero []) BinderInfo.default


def nat : Expr := .const ``Nat []

def addOne : Expr :=
  .lam `x nat
    (mkAppN (.const ``Nat.add []) #[.bvar 0, mkNatLit 1])
    BinderInfo.default

def mapAddOneNil : Expr :=
  mkAppN (.const ``List.map [levelOne, levelOne])
    #[nat, nat, addOne, .app (.const ``List.nil [levelOne]) nat]

#eval mapAddOneNil

elab "mapAddOneNil" : term => return mapAddOneNil

#check mapAddOneNil
-- List.map (fun x => Nat.add x 1) [] : List Nat

set_option pp.universes true in
set_option pp.explicit true in
#check mapAddOneNil
-- @List.map.{1, 1} Nat Nat (fun x => Nat.add x 1) (@List.nil.{1} Nat) : List.{1} Nat

#reduce mapAddOneNil
-- []
