--
--    author:  bernborgess
--    problem: 1987to2013 - lean-learn
--    created: 19.February.2024 10:31:28
--

open IO

def getLine : IO String := do return (←(←getStdin).getLine).trim

def readLn : IO Nat := do return (←getLine).toNat!

def repeats? (x : Nat) : Bool := u.length < l.length
  where
    l := x.repr.toList
    u := l.eraseDups

def finder (x : Nat) : Nat :=
  if x >= 10000 then 10234
  else if repeats? x then finder (x+1)
  else x
termination_by finder x => 10000 - x
decreasing_by
  simp_wf
  have hne : ¬x >= 10000 := by assumption
  have h0 : x < 10000 := by exact Nat.gt_of_not_le hne
  refine Nat.sub_succ_lt_self 10000 x h0


def main : IO Unit := do
  let Y ← readLn
  println $ finder (Y+1)
