--
--    author:  bernborgess
--    problem: CheeseKun - lean-learn
--    created: 01.March.2024 12:02:07
--

open IO

def getLine : IO String := do return (←(←getStdin).getLine).trim
def readLn : IO Nat := do return (←getLine).toNat!

def main : IO Unit := do
  let W ← readLn
  let C ← readLn
  let M :=
    if W = 3 ∧ C >= 95 then "absolutely"
    else if W = 1 ∧ C <= 50 then "fairly"
    else "very"
  println s!"C.C. is {M} satisfied with her pizza."
