--
--    author:  bernborgess
--    problem: CrazyFencing - lean-learn
--    created: 01.March.2024 12:20:19
--

open IO

def getLine : IO String := do return (←(←getStdin).getLine).trim
def getList : IO (List Nat) := return ((←getLine).split Char.isWhitespace).map String.toNat!

def List.sum [Add α] [OfNat α 0] : List α → α :=
  List.foldl (·+·) 0

def main : IO Unit := do
  let _ ← getLine
  let hs ← List.map Nat.toFloat <$> getList
  let bs ← List.map Nat.toFloat <$> getList
  let area := λ ((x,y),b) ↦ b * (min x y) + ((x - y).abs * b) / 2.0
  let Ts := (hs.zip hs.tail!).zip bs
  println $ (Ts.map area).sum
