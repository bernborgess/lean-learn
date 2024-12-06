--
--    author:  bernborgess
--    problem: IconScaling - lean-learn
--    created: 27.February.2024 21:10:34
--

open IO List String

def getLine : IO String := do return (←(←getStdin).getLine).trim
def readLn : IO Nat := do return (←getLine).toNat!

def icon := ["*x*"," xx","* *"].map toList

def kTimes (k : Nat) (xs : List α) : List α :=
  join $ map (replicate k ·) xs

def main : IO Unit := do
  let k ← readLn
  let ans := kTimes k (icon.map (kTimes k))
  (ans.map mk).forM println
