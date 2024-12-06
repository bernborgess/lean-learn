--
--    author:  bernborgess
--    problem: ASpookySeason - lean-learn
--    created: 12.February.2024 19:10:38
--

open IO List

def getLine : IO String := do return (←(←getStdin).getLine).trim

def readLn : IO Nat := do return (←getLine).toNat!

def main : IO Unit := do
  let S ← readLn
  let oo := asString $ map (λ _ ↦ 'o') $ range S
  println s!"sp{oo}ky"
