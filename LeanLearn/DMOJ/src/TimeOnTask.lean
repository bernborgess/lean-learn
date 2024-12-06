--
--    author:  bernborgess
--    problem: TimeOnTask - lean-learn
--    created: 26.February.2024 10:43:57
--

open IO

def replicateM : Nat → IO α → IO (List α)
| 0, _     => return []
| k + 1, f => return (←f) :: (←replicateM k f)

def getLine : IO String := do return (←(←getStdin).getLine).trim
def readLn : IO Nat := do return (←getLine).toNat!

def sort [LT α] [DecidableRel ((·<·) : α → α → Prop)] : List α → List α :=
  Array.toList ∘ flip Array.qsort (·<·) ∘ Array.mk

def main : IO Unit := do
  let T ← readLn
  let C ← readLn
  let xs ← sort <$> replicateM C readLn
  let (_,c) := xs.foldl (λ (s,c) x => if s + x <= T then (s+x,c+1) else (s,c)) (0,0)
  println c
