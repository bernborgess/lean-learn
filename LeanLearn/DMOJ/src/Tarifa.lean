--
--    author:  bernborgess
--    problem: Tarifa - lean-learn
--    created: 06.March.2024 23:08:05
--

open IO

def replicateM : Nat → IO α → IO (List α)
| 0, _     => return []
| k + 1, f => return (←f) :: (←replicateM k f)

def getLine : IO String := do return (←(←getStdin).getLine).trim
def readLn : IO Nat := do return (←getLine).toNat!

def List.sum [Add α] [OfNat α 0] : List α → α :=
  List.foldl (·+·) 0

def main : IO Unit := do
  let X ← readLn
  let N ← readLn
  let Ps ← replicateM N readLn
  println $ (N+1) * X - Ps.sum
