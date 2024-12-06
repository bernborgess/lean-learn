--
--    author:  bernborgess
--    problem: RollTheDice - lean-learn
--    created: 25.February.2024 21:31:14
--

open IO

def getLine : IO String := do return (←(←getStdin).getLine).trim
def readLn : IO Nat := do return (←getLine).toNat!

def main : IO Unit := do
  let m ← min 9 <$> readLn
  let n ← min 9 <$> readLn
  let x := m - (9 - n)
  if x == 1 then println "There is 1 way to get the sum 10."
  else println s!"There are {x} ways to get the sum 10."
