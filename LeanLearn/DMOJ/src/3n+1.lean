--
--    author:  bernborgess
--    problem: 3n+1 - lean-learn
--    created: 11.June.2024 15:10:28
--

open IO

def getLine : IO String := do return (←(←getStdin).getLine).trim
def readLn : IO Nat := do return (←getLine).toNat!

def next (n : Nat) :=
  if 2 ∣ n then n / 2
  else 3 * n + 1

partial def seq (n : Nat) :=
  if n = 1 then 0
  else 1 + (seq $ next n)

def main : IO Unit := do
  let n ← readLn
  println $ seq n
