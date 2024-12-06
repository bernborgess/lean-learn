import Mathlib.Data.Nat.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem just_calc_it : 1 = 1 := by
  rfl
  done

theorem equals_itself (n : ℕ) : n = n := by
  rfl
  done

def id₁ (x : α) : α := x

theorem apply_but_same (n : ℕ) : id₁ n = n := by
  rfl
  done

theorem add_zero_does_nothing (n : ℕ) : 0 + n = n := by
  apply Nat.add_comm
  done

theorem distribute_prod_over_add (x y z : ℕ) : x * (y + z) = x * y + x * z := by
  apply Nat.mul_add
  done

namespace Logs
open Real

theorem logarithm_of_prod_is_sum_of_logs (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) :
  log (x * y) = log x + log y :=
  log_mul hx hy

theorem logartihm_plus_log_1_same : ∀ x : ℝ, log x + log 1 = log x := by
  intro x
  have h : log 1 = 0 := by exact log_one
  rw [h]
  exact add_zero (log x)
  done

end Logs

theorem x2_ge_x : ∀ x : ℝ, x ^ 2 + x >= x := by
  intro x
  have h_gt_0 : x ^ 2 >= 0 := by exact sq_nonneg x
  exact le_add_of_nonneg_left h_gt_0
  done

theorem mult_both_sides (a b x : ℕ) : a >= b → x * a >= x * b := by
  exact λ a => Nat.mul_le_mul Nat.le.refl a
  done

theorem rm_x_both_sides (a b x : ℕ) : x > 0 → x * a >= x * b → a >= b := by
  intro h0 hxab
  exact Nat.le_of_mul_le_mul_left hxab h0
  done

theorem squared_iff_times_itself (x : ℕ) : x^2 = x * x := by
  exact Nat.pow_two x
  done

theorem x_ge_0_imp_x2_ge_x : ∀ x : ℕ, x > 0 → x^2 >= x := by
  intro x _h0
  rw [Nat.pow_two]
  exact Nat.le_mul_self x
  done

theorem log2_x_le_x : Nat.log2 x <= x := by
  exact Nat.log2_le_self x
  done

namespace MyNat


def after_pattern (n : ℕ) :=
  if n == 0 then
    have : n = 0 := sorry
    0
  else
    have : n > 0 := sorry
    1

-- theorem after_pattern_is_not_pattern
  -- intro h0 h1
  -- sorry
  -- done

def log2₀ (x : ℕ) : ℕ := go x 0 where
  go
  | 0,_ => 0
  | 1,y => y
  | x,y =>
    have : x > 1 := sorry
    have : x / 2 < x := Nat.log2_terminates x this
    go (x/2) (y+1)


def log2 (x : ℕ) : ℕ :=
  if h0 : x > 1 then
    go x 1 h0
  else 0
  where
  go (x y : ℕ) (h : x > 1) : ℕ :=
    have : x / 2 < x := Nat.log2_terminates x h
    if h0 : x / 2 > 1 then
      go (x/2) (y+1) h0
    else y

/-!
  -- go
  -- | 0,_ => 0
  -- | 1,y => y
  -- | x,y =>
  --   have : x > 1 := sorry
  --   have : x / 2 < x := Nat.log2_terminates x this
  --   go (x/2) (y+1)

-/

def xs := List.range 100

/-!
-
-- #eval List.

-- def repeated (x : α) : List α := xs where
--   xs := x :: xs

-- #eval List.take 3 (repeat 3)

-- def ExpTwoList (n : ℕ) : List ℕ :=
--   List.replicate (2^n) n

-- #eval ExpTwoList 3


-- def GenLogs (n : ℕ) :=
--   List.take n $ (0::·) $ List.join $ List.map ExpTwoList $ List.range n

-- #eval GenLogs 10
-/

def log2xs := [0,0,1,1,2,2,2,2,3,3,3,3,3,3,3,3,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6]
-- #eval List.and $ (List.range 10).map (λ x => x == log2 x)

#eval (xs.map λ x => log2 x).zip log2xs
#eval List.and $ xs.zipWith (λ x y => log2 x == y) log2xs

end MyNat

example : 3 > 0 := by
  exact Nat.le.step (Nat.le.step Nat.le.refl)
  done

theorem _10_gt_0 : 10 > 0 := by
  exact Nat.succ_pos 9

theorem _35_gt_0 : 35 > 0 := by
  exact Nat.succ_pos 34

theorem _100_gt_0 : 100 > 0 := by
  exact Nat.succ_pos 99

theorem n_minus_1_lt_n : ∀ n : Nat, n > 0 → n - 1 < n := by
  intro n h
  exact Nat.sub_one_lt_of_le h Nat.le.refl
  done

theorem some_theorem (a b : Int) :
  a * a + a * b - b * b - a * b =
  a * a + a * b - a * b - b * b :=
  calc
    a * a + a * b - b * b - a * b =
    a * a + a * b - a * b - b * b := by rw [@sub_right_comm]

theorem some_theorem₂ (a b : Int) :
  a * a + a * b - a * b - b * b =
  a * a - b * b :=
  calc
    a * a + a * b - a * b - b * b =
    a * a - b * b := by rw [Int.add_sub_cancel]

example : ¬x ≥ 10000 → x < 10000 := by
  intro hn_x_ge_thou
  exact Nat.not_le.mp hn_x_ge_thou
  done

theorem not_lt_imp_ge (P N : Nat) : ¬P < N → P >= N := by
  intro h
  exact Nat.ge_of_not_lt h
  done

theorem my_ne_of_apply_ne {α β : Sort _} (f : α → β) {x y : α} : f x ≠ f y → x ≠ y :=
  mt <| congrArg _

theorem not_eq_zero_imp_gt_zero (P R N : Nat) : ¬(R == 0) = true → R > 0 := by
  intro h
  have hR_ne_0 : R ≠ 0 := ne_of_apply_ne (fun R => R == 0) h
  apply Nat.pos_of_ne_zero hR_ne_0
  done

#check @Nat.sub_add_comm
-- P (N * (R+1)) N

theorem use_sub_add_comm (P R N : Nat) (h : P >= N):
  P + N * (R + 1) - N = P - N + N * (R + 1) := by
  apply Nat.sub_add_comm
  apply h
  done


theorem nat_lt (P R N : Nat) (h1 : P >= N) (h2 : R > 0) (h3 : N > 0)
  : P - N * (R + 1) < P - N := by
  have h4  : 1 < R + 1                                 := Nat.lt_add_of_pos_left h2
  have h5  : N < N * (R + 1)                           := lt_mul_right h3 h4
  have h6  : P + N < P + N * (R + 1)                   := Nat.add_lt_add_left h5 P
  have h7  : P < P + N * (R + 1) - N                   := Nat.lt_sub_of_add_lt h6
  have h8  : P + N * (R + 1) - N = P - N + N * (R + 1) := Nat.sub_add_comm h1
  have h9  : P < P - N + N * (R + 1)                   := Nat.lt_of_lt_of_eq h7 h8

  have hk  : P >= N * (R + 1)                          := by sorry

  have h10 : P - N * (R + 1) < P - N                   := Nat.sub_lt_right_of_lt_add hk h9
  exact h10
  done

theorem rw_in_lt (a b c : Nat) (h1 : b = c) (h2 : a < b) : a < c := by
  exact Nat.lt_of_lt_of_eq h2 h1
  done

theorem rw_in_lt2 (P R N : Nat) (h1 : P >= N) (h2 : P < P + N * (R + 1) - N) :
  P < P - N + N * (R + 1) := by
  -- rw [use_sub_add_comm P N (N * (R + 1)) h1]
  sorry
  done

theorem always_lt (P R N : Int) (hR_gt_0: R > 0) (hN_gt_0: N > 0):
  P - N * (R + 1) < P - N := by
  have h1 : 1 < R + 1                    := by exact Int.lt_add_one_iff.mpr hR_gt_0
  have h2 : N < N * (R + 1)              := lt_mul_right hN_gt_0 h1
  have h3 : P - N * (R + 1) < P - N      := by exact Int.sub_lt_sub_left h2 P
  exact h3
  done

theorem useful_theorem_on_nat (a b c : ℕ) (h1 : b <= a) (h2 : a < c + b) :
 a - b < c := by
  -- exact Nat.sub_lt_left_of_lt_add h1 h2
  exact Nat.sub_lt_right_of_lt_add h1 h2
  done







theorem prod_gt_0 (a b : Nat) (ha : 0 < a) (hb : 0 < b):
  0 < a * b := by
  exact Nat.mul_pos ha hb
  done

theorem sub_c (a b c : Nat) (h1 : a < b) (h2: c <= a) :
  a - c < b - c := by
  exact tsub_lt_tsub_right_of_le h2 h1
  done

theorem sub_parens (a b c : Nat) : a - b - c = a - (b + c) := by
  exact Nat.sub_sub a b c
  done

#check Nat.sub_sub

theorem epidemic_terminates? (P N R X S: Nat)
  (h1: ¬S > P)
  (h2: ¬(N == 0) = true)
  (h3: ¬(R == 0) = true)
  : P - (S + N * R) < P - S := by

  have ha : N * R <= P              := by sorry
  have hb : S <= P - N * R          := sorry

  have h1 : S <= P                  := by exact not_lt_imp_ge P S h1
  have h2 : 0 < N                   := by exact not_eq_zero_imp_gt_zero P N P h2
  have h3 : 0 < R                   := by exact not_eq_zero_imp_gt_zero P R P h3
  have h4 : 0 < N * R               := by exact Nat.mul_pos h2 h3
  have h5 : P < P + N * R           := by exact Nat.lt_add_of_pos_right h4
  have h6 : P - N * R < P           := by exact Nat.sub_lt_right_of_lt_add ha h5
  have h7 : P - N * R - S < P - S   := by exact tsub_lt_tsub_right_of_le hb h6
  have h8 : P - (N * R + S) < P - S := by rw[←Nat.sub_sub P (N*R) S] ; exact h7
  have h9 : P - (S + N * R) < P - S := by rw[Nat.add_comm]; exact h8
  exact h9
  done

theorem neq_of_neq (A B : Nat) (h : ¬(A == B) = true) : A ≠ B := by
  sorry
  done

#check Nat.eq_of_beq_eq_true

-- PNRXS: Nat
-- h✝³: ¬S > P
-- h✝²: ¬S = P
-- h✝¹: ¬N = 0
-- h✝: ¬R = 0
-- ⊢ P - (S + N * R) < P - S

theorem epidemic_terminates (P N R X S: Nat)
  (h1: ¬S > P)
  (h2: ¬S = P)
  (h3: ¬N = 0)
  (h4: ¬R = 0)
  : P - (S + N * R) < P - S := by
  apply Nat.sub_lt_sub_left <;> simp at * <;> omega
  done

#print epidemic_terminates

theorem epidemic_terminates3 (P N R X S: Nat)
  (h1: ¬S > P)
  (hPS : ¬(S == P) = true)  -- <-- note the extra assumption
  (h2: ¬(N == 0) = true)
  (h3: ¬(R == 0) = true)
  : P - (S + N * R) < P - S := by
  rw [beq_iff_eq] at *
  apply Nat.sub_lt_sub_left
  · exact Nat.lt_of_le_of_ne (Nat.ge_of_not_lt ‹_›) ‹_›
  · conv => left; rw [← Nat.add_zero S]
    apply Nat.add_lt_add_left (Nat.mul_pos ?_ ?_)
    · cases N
      · contradiction
      · apply Nat.succ_pos
    · cases R
      · contradiction
      · apply Nat.succ_pos
  done
