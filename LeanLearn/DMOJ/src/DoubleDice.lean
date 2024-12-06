--
--    author:  bernborgess
--    problem: DoubleDice - lean-learn
--    created: 12.February.2024 19:19:18
--

open IO

def replicateM : Nat → IO α → IO (List α)
| 0, _     => return []
| k + 1, f => return (←f) :: (←replicateM k f)

def getLine : IO String := do return (←(←getStdin).getLine).trim

def readLn : IO Nat := do return (←getLine).toNat!

def getList : IO (List Int) := return ((←getLine).split Char.isWhitespace).map String.toInt!

def getTuple : IO (Int × Int) := do
  let xs ← getList
  return (xs.head!, xs.tail!.head!)

def agg : Int × Int → Int × Int → Int × Int
| (a,d),(x,y) => match compare x y with
  | .lt => (a-y,d)
  | .eq => (a,d)
  | .gt => (a,d-x)

def main : IO Unit := do
  let n ← readLn
  let xs ← replicateM n getTuple
  let (a,d) := xs.foldl agg (100,100)
  println a
  println d
