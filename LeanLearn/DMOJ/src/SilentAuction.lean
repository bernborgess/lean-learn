--
--    author:  bernborgess
--    problem: SilentAuction - lean-learn
--    created: 01.March.2024 11:41:52
--

open IO

def replicateM : Nat → IO α → IO (List α)
| 0, _     => return []
| k + 1, f => return (←f) :: (←replicateM k f)

def getLine : IO String := do return (←(←getStdin).getLine).trim
def readLn : IO Nat := do return (←getLine).toNat!

abbrev Bid := String × Nat

def List.sort : List Bid → List Bid :=
  Array.toList ∘ flip Array.insertionSort (·.snd > ·.snd) ∘ Array.mk

def main : IO Unit := do
  let N ← readLn
  let bids ← replicateM N do return (←getLine,←readLn)
  println $ bids.sort.head!.fst
