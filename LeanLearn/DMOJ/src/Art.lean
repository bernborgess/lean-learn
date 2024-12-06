--
--    author:  bernborgess
--    problem: Art - lean-learn
--    created: 05.March.2024 19:35:36
--

open IO

def replicateM : Nat → IO α → IO (List α)
| 0, _     => return []
| k + 1, f => return (←f) :: (←replicateM k f)

def getLine : IO String := do return (←(←getStdin).getLine).trim
def readLn : IO Nat := do return (←getLine).toNat!

def getPair : IO (Int × Int) := do
  let k := (←getLine).split (·=',')
  return (k.head!.toNat!,k.tail!.head!.toNat!)

def main : IO Unit := do
  let N ← readLn
  let xys ← replicateM N getPair
  let Mx := xys.foldl (λ a (x,_) => max x a) 0
  let mx := xys.foldl (λ a (x,_) => min x a) 999
  let My := xys.foldl (λ a (_,y) => max y a) 0
  let my := xys.foldl (λ a (_,y) => min y a) 999
  println s!"{mx-1},{my-1}"
  println s!"{Mx+1},{My+1}"
