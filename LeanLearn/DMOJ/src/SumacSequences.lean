--
--    author:  bernborgess
--    problem: SumacSequences - lean-learn
--    created: 27.February.2024 21:41:11
--

open IO

def getLine : IO String := do return (←(←getStdin).getLine).trim
def readLn : IO Nat := do return (←getLine).toNat!

partial def recur (x y : Nat) :=
  if x < y then 2 else
  1 + recur y (x - y)

def main : IO Unit := do
  let t₁ ← readLn
  let t₂ ← readLn
  println $ recur t₁ t₂
