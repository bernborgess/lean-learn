import Lean
open Lean Expr Elab Level

-- 1. Create expression 1 + 2 with Expr.app.

def onePlusTwo := Expr.app (Expr.app (.const ``Nat.add []) (.bvar 1)) (.bvar 2)
#eval onePlusTwo

-- 2. Create expression 1 + 2 with Lean.mkAppN.

def onePlusTwo' := Lean.mkAppN (.const ``Nat.add []) #[.bvar 1, .bvar 2]
#eval onePlusTwo'

-- 3. Create expression fun x => 1 + x.

def nat : Expr := .const ``Nat []

def incX :=
  Expr.lam `x nat
    (mkAppN (.const ``Nat.add []) #[.bvar 1, mkNatLit 1])
    BinderInfo.default

-- 4. [De Bruijn Indexes] Create expression fun a, fun b, fun c, (b * a) + c.

def bruj : Expr :=
  .lam `a nat (
    .lam `b nat (
      .lam `c nat (
        mkAppN (.const ``Nat.add [])
        #[ mkAppN (.const ``Nat.mul []) #[.bvar 1, .bvar 2],
          .bvar 0 ]
      ) BinderInfo.default
    ) BinderInfo.default
  ) BinderInfo.default

#eval bruj
elab "bruj" : term => return bruj
#check bruj

-- 5. Create expression fun x y => x + y.

def adder : Expr :=
  .lam `x nat (
    .lam `y nat (
      mkAppN (.const ``Nat.add []) #[.bvar 1,.bvar 0]
    ) BinderInfo.default
  ) BinderInfo.default

#eval adder
elab "adder" : term => return adder
#check adder

-- 6. Create expression fun x, String.append "hello, " x.

def string: Expr := .const ``String []

def appender : Expr :=
  .lam `x string (
    mkAppN (.const ``String.append []) #[ mkStrLit "hello, " , .bvar 0 ]
  ) BinderInfo.default

#eval appender
elab "appender" : term => return appender
#check appender

-- 7. Create expression ∀ x : Prop, x ∧ x.

def prop : Expr := Expr.sort Level.zero



def xandx : Expr :=
  .forallE `x prop (
    mkAppN (.const ``And []) #[.bvar 0,.bvar 0]
  )
  BinderInfo.default

#eval xandx
elab "xandx" : term => return xandx
#check xandx

-- 8. Create expression Nat → String.

def retStr : Expr :=
  .lam `x nat (mkStrLit "hi") BinderInfo.default

#eval retStr
elab "retStr" : term => return retStr
#check retStr

-- 9. Create expression fun (p : Prop) => (λ hP : p => hP).

def constantProof : Expr :=
  .lam `p prop (
    .lam `hP (.bvar 1) (
      .bvar 0
    ) BinderInfo.default
  ) BinderInfo.default

#eval constantProof
elab "constantProof" : term => return constantProof
#check constantProof

-- 10. [Universe levels] Create expression Type 6.

def t6 : Expr := Lean.Expr.sort
  (Lean.Level.succ
  (Lean.Level.succ
  (Lean.Level.succ
  (Lean.Level.succ
  (Lean.Level.succ
  (Lean.Level.succ
  (Lean.Level.succ
  (Lean.Level.zero)
  )))))))

#eval t6
elab "t6" : term => return t6
#check t6
