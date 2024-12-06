--
--    author:  bernborgess
--    problem: MagicSquares - lean-learn
--    created: 23.February.2024 21:46:08
--

open IO

def replicateM : Nat → IO α → IO (List α)
| 0, _     => return []
| k + 1, f => return (←f) :: (←replicateM k f)

def getLine : IO String := do return (←(←getStdin).getLine).trim
def getList : IO (List Int) := return ((←getLine).split Char.isWhitespace).map String.toInt!

def sum : List Int → Int :=  List.foldl (·+·) 0

def List.transpose (l : List (List α)) : List (List α) := (l.foldr go #[]).toList where
  pop (old : List α) : StateM (List α) (List α)
  | [] => (old, [])
  | a :: l => (a :: old, l)
  go (l : List α) (acc : Array (List α)) : Array (List α) :=
    let (acc, l) := acc.mapM pop l
    l.foldl (init := acc) λ arr a => arr.push [a]

def equals [BEq α]: List α → Bool
| x :: xs => xs.all (· == x)
| [] => false

def main : IO Unit := do
  let xxs ← replicateM 4 getList
  let l := xxs.map sum
  let t := xxs.transpose.map sum
  if equals $ l ++ t then
    println "magic"
  else
    println "not magic"
