--
--    author:  bernborgess
--    problem: VoteCount - lean-learn
--    created: 12.February.2024 13:35:49
--

open IO List

def getLine : IO String := do return (←(←IO.getStdin).getLine).trim

def getList : IO (List Char) := do return (←getLine).toList

def sing | 'A' => 1 | 'B' => -1 | _ => 0

def main : IO Unit := do
  let _ ← getLine
  let v ← getList
  let diff := foldl (· + sing ·) 0 v
  let res := match compare diff 0 with
    | .lt => "B" | .eq => "Tie" | .gt => "A"
  println res
