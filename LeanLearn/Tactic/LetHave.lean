-- How to add content to the context
import Lean

open Lean Elab Tactic Meta

-- Some description of it
elab "custom_let " n:ident " : " t:term " := " v:term : tactic =>
  withMainContext do
    let t ← elabTerm t none
    let v ← elabTermEnsuringType v t
    liftMetaTactic fun mvarId => do
      let mvarIdNew ← mvarId.define n.getId t v
      let (_,mvarIdNew) ← mvarIdNew.intro1P
      return [mvarIdNew]

elab "custom_have" n:ident " : " t:term " := " v:term : tactic =>
  withMainContext do
    let t ← elabTerm t none
    let v ← elabTermEnsuringType v t
    liftMetaTactic fun mvarId => do
      let mvarIdNew ← mvarId.assert n.getId t v
      let (_, mvarIdNew) ← mvarIdNew.intro1P
      return [mvarIdNew]

theorem test_custom_let : True := by
  custom_let n : Nat := 5
  custom_have h : n = n := rfl
  -- exact (5 == n)
  trivial
