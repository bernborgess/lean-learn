--
--    author:  bernborgess
--    problem: ANewHope - lean-learn
--    created: 14.February.2024 21:27:41
--

open IO List

def getLine : IO String := do return (←(←getStdin).getLine).trim

def readLn : IO Nat := do return (←getLine).toNat!

def main : IO Unit := do
  let N ← readLn
  let far := String.join $ map (λ _ => "far, ") $ range (N-1)
  println s!"A long time ago in a galaxy {far}far away..."
