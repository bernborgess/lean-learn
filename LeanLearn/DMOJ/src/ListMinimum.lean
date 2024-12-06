--
--    author:  bernborgess
--    problem: ListMinimum - lean-learn
--    created: 23.February.2024 21:38:15
--

open IO

def replicateM : Nat → IO α → IO (List α)
| 0, _     => return []
| k + 1, f => return (←f) :: (←replicateM k f)

def getLine : IO String := do return (←(←getStdin).getLine).trim
def readLn : IO Nat := do return (←getLine).toNat!

def List.sort [LT α] [DecidableRel ((·<·) : α → α → Prop)] : List α → List α :=
  Array.toList ∘ flip Array.qsort (·<·) ∘ Array.mk

def main : IO Unit := do
  let N ← readLn
  let xs ← replicateM N readLn
  xs.sort.forM println
