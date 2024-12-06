--
--    author:  bernborgess
--    problem: QuadrantSelection - lean-learn
--    created: 12.February.2024 00:52:13
--

open IO

def readLn : IO Int := do return (←(←IO.getStdin).getLine).trim.toInt!

def main : IO Unit := do
  let x ← readLn
  let y ← readLn
  let ans := match (compare x 0,compare y 0) with
  | (.gt,.gt) => 1
  | (.lt,.gt) => 2
  | (.lt,.lt) => 3
  | (.gt,.lt) => 4
  | _ => 0
  println ans
