import Mathlib.Tactic.SimpRw

#check List.length_filter_le
/- List.length_filter_le.{u_1}
\  {α : Type u_1} (p : α → Bool) (l : List α)
\  : (List.filter p l).length ≤ l.length 
\  -/

theorem List.length_filter_tail_lt (xs : List Int) (p : Int → Bool)
  (xs_not_empty : xs ≠ [])
  : (xs.tail.filter p).length < xs.length := by
  obtain ⟨h,t,xs_eq_ht⟩ := xs.exists_cons_of_ne_nil xs_not_empty
  have xs_tail_eq_t : xs.tail = t := by rw [xs_eq_ht]; apply t.tail_cons
  have xs_head_eq_h : xs.head xs_not_empty = h := by simp_rw [xs_eq_ht]; rfl
  have p1 : (xs.tail.filter p).length ≤ t.length :=  by
    rw [xs_tail_eq_t]; apply length_filter_le p t
  have p2 : t.length < xs.length := by
    rw [xs_eq_ht]; exact Nat.lt_add_one t.length
  apply Nat.lt_of_le_of_lt p1 p2
  
def quick : List Int → List Int
| [] => []
| h::t => 
  let less := t.filter (· < h)
  let more := t.filter (· ≥ h)
  have : less.length < (h::t).length :=
    (h::t).length_filter_tail_lt (λ x ↦ x < h) (t.cons_ne_nil h)
  have : more.length < (h::t).length := 
    (h::t).length_filter_tail_lt (λ x ↦ x ≥ h) (t.cons_ne_nil h)
  quick less ++ [h] ++ quick more
termination_by xs => xs.length

