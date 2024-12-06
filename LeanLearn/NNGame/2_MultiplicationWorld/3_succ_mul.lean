import Mathlib.Data.Nat.Defs

open Nat


theorem succ_mul (a b : ℕ) : succ a * b = a * b + b := by
  sorry
  done

#check Nat.add_assoc
#check Nat.add_comm
#check Nat.add_right_comm


theorem finalize (a d : ℕ) :
  a * d + d + (a + 1) = a * d + a + (d + 1) :=
  by
  rw [←Nat.add_assoc]

  rw [←Nat.add_assoc]

  rw [Nat.add_comm (a * d + a)]

  rw [Nat.add_comm (a * d)]

  rw [←Nat.add_assoc]

  done
