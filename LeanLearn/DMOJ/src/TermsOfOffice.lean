--
--    author:  bernborgess
--    problem: TermsOfOffice - lean-learn
--    created: 23.February.2024 00:35:40
--

open IO

def getLine : IO String := do return (←(←getStdin).getLine).trim
def readLn : IO Nat := do return (←getLine).toNat!

def main : IO Unit := do
  let X ← readLn
  let Y ← readLn
  let A := (Y - X) / 60 + 1
  (List.range A).forM λ k =>
    println s!"All positions change in year {X+k*60}"
