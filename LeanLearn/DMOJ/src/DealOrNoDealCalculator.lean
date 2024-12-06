--
--    author:  bernborgess
--    problem: DealOrNoDealCalculator - lean-learn
--    created: 25.February.2024 09:11:41
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
  let n ← readLn
  let opened ← replicateM n readLn
  let offer ← readLn
  let brief := [10^6,5*10^5,10^5,50000,25000,10^4,5000,1000,500,100].zip $ List.iota 10
  let available := brief.filter (!opened.contains ·.snd)
  let bonus := (available.map (·.fst)).sum
  if bonus < offer * available.length then
    println "deal"
  else
    println "no deal"
