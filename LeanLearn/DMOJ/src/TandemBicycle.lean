--
--    author:  bernborgess
--    problem: TandemBicycle - lean-learn
--    created: 23.February.2024 12:22:47
--

open IO

def getLine : IO String := do return (←(←getStdin).getLine).trim
def readLn : IO Nat := do return (←getLine).toNat!
def getList : IO (List Nat) := return ((←getLine).split Char.isWhitespace).map String.toNat!

def sort [LT α] [DecidableRel ((·<·) : α → α → Prop)  ] : List α → List α :=
  Array.toList ∘ flip Array.qsort (·<·) ∘ Array.mk

def main : IO Unit := do
  let t ← readLn
  let _ ← readLn
  let dmoj ← sort <$> getList
  let peg ← (if t = 2 then List.reverse else id) <$> sort <$> getList
  let ans := List.foldl (·+·) 0 $ dmoj.zipWith max peg
  println ans
