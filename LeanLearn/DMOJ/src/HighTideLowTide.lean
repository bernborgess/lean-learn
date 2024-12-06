--
--    author:  bernborgess
--    problem: HighTideLowTide - lean-learn
--    created: 28.February.2024 07:57:44
--

open IO

def getLine : IO String := do return (←(←getStdin).getLine).trim
def readLn : IO Nat := do return (←getLine).toNat!

def getList : IO (List Nat) := return ((←getLine).split Char.isWhitespace).map String.toNat!
def printList [ToString α] : List α → IO Unit := println ∘ String.join ∘ List.intersperse " " ∘ List.map toString

def List.splitAt (n : Nat) (l : List α) : List α × List α := go l n #[] where
  go : List α → Nat → Array α → List α × List α
  | [], _, _ => (l, [])
  | x :: xs, n+1, acc => go xs n (acc.push x)
  | xs, _, acc => (acc.toList, xs)

def sort [LT α] [DecidableRel ((·<·) : α → α → Prop)] : List α → List α :=
  Array.toList ∘ flip Array.qsort (·<·) ∘ Array.mk

def main : IO Unit := do
  let N ← readLn
  let xs ← sort <$> getList
  let (ls,hs) := xs.splitAt ((N+1)/2)
  let fixEnd := cond (N % 2 == 1) (flip List.eraseIdx N) id
  printList $ fixEnd $ List.join $ ls.reverse.zipWith ([·,·]) (hs++[0])
