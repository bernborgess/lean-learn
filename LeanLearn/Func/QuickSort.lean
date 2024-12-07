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

def quick_sort [LT α] [LE α]
  [DecidableRel ((·<·) : α → α → Prop)]
  [DecidableRel ((·≥·) : α → α → Prop)]
  : List α → List α
| [] => []
| h::t =>
  let less := t.filter (· < h)
  let more := t.filter (· ≥ h)

  -- Termination proof
  have : less.length < (h::t).length :=
    (h::t).length_filter_tail_lt (· < h) (t.cons_ne_nil h)
  have : more.length < (h::t).length :=
    (h::t).length_filter_tail_lt (· ≥ h) (t.cons_ne_nil h)

  quick_sort less ++ [h] ++ quick_sort more

termination_by xs => xs.length

/- theorem complementary [LT α] [LE α] -/
/-   [DecidableRel ((·<·) : α → α → Prop)] -/
/-   [DecidableRel ((·≥·) : α → α → Prop)] -/
/-   (x : α) -/
/-   : ∀y:α, (y < x) ∨ (y ≥ x) -/

theorem Nat.complementary
  (x : Nat)
  : ∀y:Nat, (y < x) ∨ (y ≥ x)
  := by
  intro y

  exact Nat.lt_or_ge y x
#check Nat.lt_or_ge

def partition_lt_ge_prop
  (x : Nat)
  (l : List Nat)
  :=
  let less := l.filter (· < x)
  let more := l.filter (· ≥ x)
  ∀ y : Nat, y ∈ l → y ∈ less ∨ y ∈ more

-- #check le_of_not_lt

example (x : Nat) (l : List Nat) : partition_lt_ge_prop x l := by
  simp only [partition_lt_ge_prop, List.mem_filter, decide_eq_true_eq, ge_iff_le]
  intro y y_in_l
  by_cases h_lt : y < x
  . left; exact ⟨y_in_l,h_lt⟩
  . right;
    have h_ge : x ≤ y := Nat.le_of_not_lt h_lt
    exact ⟨y_in_l,h_ge⟩

theorem List.filter_lt_or_ge.{u} {α : Type u} (p : α → Bool) (xs : List α)
  (xs_not_empty : xs ≠ [])
  : (xs.tail.filter p).length < xs.length := by
  /- obtain ⟨h,t,xs_eq_ht⟩ := xs.exists_cons_of_ne_nil xs_not_empty -/
  /- apply Nat.lt_of_le_of_lt -/
  sorry


theorem quick_sort_length_eq
  [LT α] [LE α]
  [DecidableRel ((·<·) : α → α → Prop)]
  [DecidableRel ((·≥·) : α → α → Prop)]
  (xs : List α)
  : (quick_sort xs).length = xs.length
  := by
  induction xs with
  | nil => simp only [List.length_nil, List.length_eq_zero, quick_sort]
  | cons h t tail_hi =>
    simp only [List.length_cons, quick_sort]


    sorry

#eval quick_sort [1,2,5,4,3]
