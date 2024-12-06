--
--    author:  bernborgess
--    problem: Sorting - lean-learn
--    created: 19.February.2024 20:20:34
--

open IO

def replicateM : Nat → IO α → IO (List α)
| 0, _     => return []
| k + 1, f => return (←f) :: (←replicateM k f)

def getLine : IO String := do return (←(←getStdin).getLine).trim
def readLn : IO Nat := do return (←getLine).toNat!


def sortInts : List Int → List Int :=
  Array.toList ∘ flip Array.qsort (·<·) ∘ Array.mk

def sort [LT α] [DecidableRel ((·<·) : α → α → Prop)] : List α → List α :=
  Array.toList ∘ flip Array.qsort (·<·) ∘ Array.mk


def main : IO Unit := do
  let n ← readLn
  let xs ← replicateM n readLn
  for x in flip Array.qsort (·<·) $ Array.mk xs do
    println x
