--
--    author:  bernborgess
--    problem: BoilingWater - lean-learn
--    created: 25.February.2024 10:12:52
--

open IO

def getLine : IO String := do return (←(←getStdin).getLine).trim
def readLn : IO Nat := do return (←getLine).toNat!

def main : IO Unit := do
  let B ← readLn
  let P := 5 * B - 400
  println P
  println $ (λ | .lt => 1 | .eq => 0 | .gt => -1) $ Ord.compare P 100
