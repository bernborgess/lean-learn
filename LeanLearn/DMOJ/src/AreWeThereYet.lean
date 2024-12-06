--
--    author:  bernborgess
--    problem: AreWeThereYet - lean-learn
--    created: 25.February.2024 12:06:02
--

open IO

def getLine : IO String := do return (←(←getStdin).getLine).trim
def getList : IO (List Int) := return ((←getLine).split Char.isWhitespace).map String.toInt!

def printList [ToString α] : List α → IO Unit :=
  println ∘ String.join ∘ List.intersperse " " ∘ List.map toString

def pref [Add α] [OfNat α 0] : List α → List α := List.reverse ∘ List.foldl go [0]
  where
  go : List α → α → List α
  | x::xs, y => (y+x) :: x :: xs
  | _    , _ => []

def main : IO Unit := do
  let xs ← pref <$> getList
  let M := xs.map λ i => xs.map λ j => (i-j).natAbs
  M.forM printList
