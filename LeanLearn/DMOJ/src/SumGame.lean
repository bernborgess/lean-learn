--
--    author:  bernborgess
--    problem: SumGame - lean-learn
--    created: 23.February.2024 22:23:14
--

open IO List Prod

def getLine : IO String := do return (←(←getStdin).getLine).trim
def readLn : IO Nat := do return (←getLine).toNat!
def getList : IO (List Int) := return ((←getLine).split Char.isWhitespace).map String.toInt!

def List.pref : List Int → List Int := List.foldl go [0]
  where
    go : List Int → Int → List Int
    | x::xs, y => (y+x) :: x :: xs
    | _    , _ => []

def main : IO Unit := do
  let N ← readLn
  let xs ← getList
  let ys ← getList
  let is := iota N ++ [0]
  println ∘ fst ∘ head! ∘ filter snd ∘ zip is $ xs.pref.zipWith (·=·) ys.pref
