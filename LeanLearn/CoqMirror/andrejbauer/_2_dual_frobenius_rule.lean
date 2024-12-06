import Lean
import Qq
open Lean Elab Tactic Qq

elab "first_order" : tactic => do
    for ldecl in ← getLCtx do
        if let some goalType ← checkTypeQ (u := levelOne) ldecl.type q(Prop) then
        if let ~q((((($a : Prop)) → $b) : Prop)) := goalType then
            let name := mkIdent ldecl.userName
            evalTactic (← `(tactic| apply $name ; assumption ))


def lem := ∀p, p ∨ ¬p
#check lem

-- * BEFORE
-- ⊢ 
-- (∀ p : Prop, p ∨ ¬p) →  
-- ∀ (A : Set) (p : A → Prop) (q : Prop),
-- (∀ x : A, q ∨ p x) ↔ q ∨ (∀ x : A, p x)
-- * AFTER
-- H : ∀ p : Prop, p ∨ ¬p
-- p : α → Prop
-- q : Prop
-- H0 : ∀ x : A, q ∨ p x
-- ⊢
-- q ∨ (∀ x : A, p x)

-- The tactic:
-- 1. Creates hypothesis
--    lem : ∀ p : Prop, p ∨ ¬p
--    H0 : ∀ x : A, q → p x
-- 2. Sets the goal to q → (∀ x : A, p x)
theorem getLem
  : ((∀ p, p ∨ ¬p) → ∀ (p : α → Prop) q, (∀ x, q ∨ p x) ↔ q ∨ ∀ x, p x)
  → (∀p, p ∨ ¬p) := by
  intro H
  

  sorry
  done


theorem fo {p : α → Prop} : (∀p, p ∨ ¬p) → (q ∨ (∀x, p x)) := by
  intro lem
  cases lem q with
  | inl hq => left ; assumption
  | inr hnq =>

    sorry
  done


def frobenius' := ∀ (α : Type) (p : α → Prop) (q : Prop),
  (∀ x : α, q ∨ p x) ↔ (q ∨ ∀ x : α, p x)

theorem lem_to_frobenius' : lem → frobenius' := by
  unfold lem frobenius'

  intro lem α p q
  constructor
  . intro haqpx
    cases lem q
    . left
      assumption
    . right
      intro x
      cases haqpx x
      . contradiction
      . assumption
  . intro hqapx
    cases hqapx
    . intro x
      left
      assumption
    . intro x
      right
      sorry

  -- match lem q with
  -- | Or.inl hq =>  try simp
  --                 sorry
  -- | Or.inr hnq => sorry
  --                 try simp

  done
