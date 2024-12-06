--
--    author:  bernborgess
--    problem: AssigningPartners - lean-learn
--    created: 28.February.2024 07:00:47
--

open IO

def getLine : IO String := do return (←(←getStdin).getLine).trim
def readLn : IO Nat := do return (←getLine).toNat!
def getList : IO (List String) := return (←getLine).split Char.isWhitespace

def main : IO Unit := do
  let _ ← readLn
  let as ← getList
  let bs ← getList
  let xs := as.zip bs
  let good := xs.all λ (a,b) ↦ a ≠ b ∧ xs.lookup b = some a
  println (cond good "good" "bad")
