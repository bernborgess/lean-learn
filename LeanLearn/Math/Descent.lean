import Mathlib.Init.Data.Nat.Basic
import Mathlib.Tactic.PushNeg
import Mathlib.Tactic.Use

-- # Descent Proof
-- if `f : ℕ → Prop`  is a property about natural numbers
-- an implication `∀x, f x → ∃y, (y < x) ∧ f y` where `y < x` will prove `f` false

theorem descent
  (f : ℕ → Prop)
  (imp : ∀x, f x → ∃y, (y < x) ∧ f y)
  : ∀x, ¬f x := by
  have k := imp 0
  sorry
  done

theorem descent_aux
  (imp : ∀x:ℕ, ∃y, (y < x))
  : False := by
  obtain ⟨y,hy⟩ := imp 0
  rcases hy -- contradiction
  done
