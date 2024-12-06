--
--    author:  bernborgess
--    problem: AnHonestDaysWork - lean-learn
--    created: 25.February.2024 12:44:10
--

open IO

def getLine : IO String := do return (←(←getStdin).getLine).trim
def readLn : IO Nat := do return (←getLine).toNat!

def main : IO Unit := do
  let P ← readLn
  let B ← readLn
  let D ← readLn
  println $ P / B * D + P % B
