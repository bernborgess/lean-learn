--
--    author:  bernborgess
--    problem: CupcakeParty - lean-learn
--    created: 28.February.2024 07:38:24
--

open IO

def getLine : IO String := do return (←(←getStdin).getLine).trim
def readLn : IO Nat := do return (←getLine).toNat!

def main : IO Unit := do
  let R ← readLn
  let S ← readLn
  println $ 8*R + 3*S - 28
