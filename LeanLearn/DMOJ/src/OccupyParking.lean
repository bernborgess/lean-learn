--
--    author:  bernborgess
--    problem: OccupyParking - lean-learn
--    created: 12.February.2024 12:30:28
--

open IO List

def getLine : IO (List Char) := do
  return (←(←IO.getStdin).getLine).trim.toList

def main : IO Unit := do
  let _ ← getLine
  let p₁ ← map (· == 'C') <$> getLine
  let p₂ ← map (· == 'C') <$> getLine
  println $ length $ filter id $ zipWith (· && ·) p₁ p₂
