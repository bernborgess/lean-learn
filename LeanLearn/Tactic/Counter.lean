import Lean

open Lean Elab Tactic Meta

syntax (name:=counter) "counter" term : tactic

def walkExpr (ex : Expr) :=
  match ex with
  | .app (.app (.const `And []) _) y => 1 + walkExpr y
  | .app _ y => walkExpr y
  | .const `And [] => 1
  | _ => 0

@[tactic counter]
def evalCounter : Tactic := λ s => do
  let xs ← elabTerm s[1] none -- Syntax → Expr
  let tp ← inferType xs
  -- count element in disjunction
  -- logInfo $ repr tp
  logInfo $ repr $ walkExpr tp

variable {p q : Prop}

example (h : p ∧ q) : p ∧ q := by
  counter h
  exact h

example (h : p ∧ q ∧ r) : p ∧ q ∧ r := by
  counter h
  exact h

-- app
--   (app (const `And []) (fvar 3348))
--   (app
--     (app (const `And []) (fvar 3350)))
--     (fvar 3359)

example (h : (p ∧ x) ∧ q ∧ r) : (p ∧ x) ∧ q ∧ r := by
  counter h
  exact h

-- app (app (and) var) (var)
