import Init.Data.Nat.Basic

def quick : List Int → List Int
| [] => []
| h::t => 
  let less := t.filter (· < h)
  let more := t.filter (· ≥ h)
  have : less.length < (h::t).length := by
    have ls_le_t : less.length ≤ t.length := by
      exact List.length_filter_le (fun x => decide (x < h)) t
    have t_lt_ht : t.length < (h::t).length := Nat.lt.base (List.length t)
    exact Nat.lt_of_le_of_lt ls_le_t t_lt_ht
  have : more.length < (h::t).length := by 
    have ls_le_t : more.length ≤ t.length := by
      exact List.length_filter_le (fun x => decide (x ≥ h)) t
    have t_lt_ht : t.length < (h::t).length := Nat.lt.base (List.length t)
    exact Nat.lt_of_le_of_lt ls_le_t t_lt_ht
  quick less ++ [h] ++ quick more
termination_by xs => xs.length


