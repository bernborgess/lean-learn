import Mathlib.Tactic.SimpRw

theorem List.length_filter_tail_lt.{u} {α : Type u} (p : α → Bool) (xs : List α) 
  (xs_not_empty : xs ≠ [])
  : (xs.tail.filter p).length < xs.length := by
  obtain ⟨h,t,xs_eq_ht⟩ := xs.exists_cons_of_ne_nil xs_not_empty
  apply Nat.lt_of_le_of_lt
  . rw [xs_eq_ht]
    exact length_filter_le p t
  . simp_rw [xs_eq_ht]
    exact Nat.lt_add_one t.length
 
def quick : List Int → List Int
| [] => []
| h::t => 
  let less := t.filter (· < h)
  let more := t.filter (· ≥ h)

  -- Termination proof
  have : less.length < (h::t).length :=
    (h::t).length_filter_tail_lt (· < h) (t.cons_ne_nil h)
  have : more.length < (h::t).length := 
    (h::t).length_filter_tail_lt (· ≥ h) (t.cons_ne_nil h)

  quick less ++ [h] ++ quick more

termination_by xs => xs.length

#eval 1 + 1
