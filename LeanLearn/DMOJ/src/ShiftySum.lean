--
--    author:  bernborgess
--    problem: ShiftySum - lean-learn
--    created: 12.February.2024 19:02:19
--

open IO List

def getLine : IO String := do return (←(←getStdin).getLine).trim

def readLn : IO Nat := do return (←getLine).toNat!

def sum (xs : List Nat) := xs.foldl (·+·) 0

def main : IO Unit := do
  let N ← readLn
  let k ← readLn
  println $ sum $ map (N * 10 ^ ·) $ range (k+1)
