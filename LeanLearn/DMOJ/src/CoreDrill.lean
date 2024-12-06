--
--    author:  bernborgess
--    problem: CoreDrill - lean-learn
--    created: 12.February.2024 13:56:55
--

open IO

def readLn : IO Nat := do return (←(←IO.getStdin).getLine).trim.toNat!

def main : IO Unit := do
  let r ← Nat.toFloat <$> readLn
  let h ← Nat.toFloat <$> readLn
  -- V = 1/3 h π r²
  let π := 3.14159
  let V := π * r ^ 2 * h / 3
  println V
