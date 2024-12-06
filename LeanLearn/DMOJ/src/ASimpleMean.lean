--
--    author:  bernborgess
--    problem: ASimpleMean - lean-learn
--    created: 02.July.2024 17:12:18
--

open IO

def getLine : IO String := do return (←(←getStdin).getLine).trim

def getList : IO (List Int) := return ((←getLine).split Char.isWhitespace).map String.toInt!

def List.sum [Add α] [OfNat α 0] : List α → α :=
  List.foldl (·+·) 0

def main : IO Unit := do
  let xs ← getList
  println <| xs.sum / 3
