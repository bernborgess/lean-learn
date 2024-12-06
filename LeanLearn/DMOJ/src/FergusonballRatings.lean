--
--    author:  bernborgess
--    problem: FergusonballRatings - lean-learn
--    created: 01.March.2024 12:07:12
--

open IO

def replicateM : Nat → IO α → IO (List α)
| 0, _     => return []
| k + 1, f => return (←f) :: (←replicateM k f)

def getLine : IO String := do return (←(←getStdin).getLine).trim
def readLn : IO Nat := do return (←getLine).toNat!

def stars := λ (points,fouls) ↦ 5 * points - 3 * fouls

def main : IO Unit := do
  let N ← readLn
  let ps ← replicateM N do pure (←readLn,←readLn)
  let stars := ps.map stars
  print $ (stars.filter (·>40)).length
  println $ if stars.all (·>40) then "+" else ""
