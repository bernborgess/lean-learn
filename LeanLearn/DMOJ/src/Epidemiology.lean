--
--    author:  bernborgess
--    problem: Epidemiology - lean-learn
--    created: 20.February.2024 11:30:33
--
open IO

def getLine : IO String := do return (←(←getStdin).getLine).trim
def readLn : IO Nat := do return (←getLine).toNat!

def epidemic (P N R X S : Nat) :=
  if S > P then X
  else if S = P then X + 1
  else if N = 0 then X
  else if R = 0 then X
  else epidemic P (N*R) R (X+1) (S+N*R)
termination_by epidemic P N R X S => P - S
decreasing_by
  simp_wf
  apply Nat.sub_lt_sub_left
  . exact Nat.lt_of_le_of_ne (Nat.ge_of_not_lt ‹_›) ‹_›
  . conv => left; rw [← Nat.add_zero S]
    apply Nat.add_lt_add_left (Nat.mul_pos ?_ ?_)
    . cases N
      . contradiction
      . apply Nat.succ_pos
    . cases R
      . contradiction
      . apply Nat.succ_pos
  done

def main : IO Unit := do
  let P ← readLn
  let N ← readLn
  let R ← readLn
  println $ epidemic P N R 0 N
