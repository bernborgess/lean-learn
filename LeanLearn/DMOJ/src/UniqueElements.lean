--
--    author:  bernborgess
--    problem: UniqueElements - lean-learn
--    created: 11.June.2024 15:20:39
--

open IO

def replicateM : Nat → IO α → IO (List α)
| 0, _     => return []
| k + 1, f => return (←f) :: (←replicateM k f)

def replicateM_ : Nat → IO Unit → IO Unit
| 0, _     => return
| k + 1, f => do f; replicateM_ k f

def getLine : IO String := do return (←(←getStdin).getLine).trim

def readLn : IO Nat := do return (←getLine).toNat!

def getList : IO (List Int) := return ((←getLine).split Char.isWhitespace).map String.toInt!

def printList [ToString α] : List α → IO Unit := println ∘ String.join ∘ List.intersperse " " ∘ List.map toString

def sort [LT α] [DecidableRel ((·<·) : α → α → Prop)] : List α → List α :=
  Array.toList ∘ flip Array.qsort (·<·) ∘ Array.mk

def List.sum [Add α] [OfNat α 0] : List α → α :=
  List.foldl (·+·) 0

#check Singleton
-- Need sets!

def main : IO Unit := do

  println "Hello World!"
