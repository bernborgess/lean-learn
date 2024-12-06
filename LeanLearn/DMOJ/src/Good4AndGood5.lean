--
--    author:  bernborgess
--    problem: Good4AndGood5 - lean-learn
--    created: 10.June.2024 14:20:54
--
-- import Mathlib.Data.Nat.Defs

open IO

def getLine : IO String := do return (←(←getStdin).getLine).trim

def readLn : IO Nat := do return (←getLine).toNat!

def ff
| (x,y) => 4 * x + 5 * y

theorem Nat.div_mul_div_comm
  {a b c d : Nat}
  : b ∣ a → d ∣ c → (a / b) * (c / d) = (a * c) / (b * d) := by
  rintro ⟨x, rfl⟩ ⟨y, rfl⟩
  obtain rfl | hb := b.eq_zero_or_pos
  · simp
  obtain rfl | hd := d.eq_zero_or_pos
  · simp
  rw [Nat.mul_div_cancel_left _ hb, Nat.mul_div_cancel_left _ hd, Nat.mul_assoc b,
    Nat.mul_left_comm x, ← Nat.mul_assoc b, Nat.mul_div_cancel_left _ (Nat.mul_pos hb hd)]

theorem Nat.mul_div_mul_comm_of_dvd_dvd
  {a b c d : Nat} (hba : b ∣ a) (hdc : d ∣ c)
  : a * c / (b * d) = a / b * (c / d) :=
  (div_mul_div_comm hba hdc).symm

theorem t1 (h : N % 4 = 0) : ff (N / 4, 0) = N := by
  unfold ff
  simp only [Nat.mul_zero, Nat.add_zero]
  rw [←Nat.div_one 4]
  have hba : 1 ∣ 4 := by exact Nat.one_dvd 4
  have hdc : (4/1) ∣ N := by exact Nat.dvd_of_mod_eq_zero h
  rw [←Nat.mul_div_mul_comm_of_dvd_dvd hba hdc]
  simp only [Nat.div_one, Nat.one_mul, Nat.zero_lt_succ, Nat.mul_div_right]
  done

theorem t2 (h : ff (x,y) = N - 1) (hx : 0 < x) (hN : 0 < N) : ff (x-1,y+1) = N := by
  unfold ff at *
  simp only at *
  rw [Nat.mul_sub_left_distrib]
  rw [Nat.mul_add, Nat.mul_one, Nat.mul_one]
  rw [Nat.add_comm, Nat.add_assoc]
  rw [←Nat.add_sub_assoc (Nat.le_mul_of_pos_right 4 hx)]
  rw [Nat.add_comm 5]
  simp only [Nat.succ_sub_succ_eq_sub, Nat.sub_zero]
  rw [←Nat.add_assoc]
  rw [Nat.add_comm (5*y)]
  rw [←Nat.eq_add_of_sub_eq hN]
  simp only [Nat.reduceSucc, h]
  done

theorem t3 (h : ff (x,4+y) = N) : ff (x+5,y) = N := by
  unfold ff at *; simp at *
  rw [Nat.mul_add] at h
  rw [Nat.mul_comm 5 4] at h
  rw [←Nat.add_assoc (4*x) (4*5) (5*y)] at h
  rw [Nat.mul_add]
  exact h
  done

def piv (x : Nat) := [1, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1].getD x 0

def solver (x : Nat) : Nat :=
  let d := x / 20
  let m := x % 20
  d + piv m

def main : IO Unit := do
  let N ← readLn
  println s!"{solver N}"
