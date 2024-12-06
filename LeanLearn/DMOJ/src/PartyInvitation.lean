--
--    author:  bernborgess
--    problem: PartyInvitation - lean-learn
--    created: 22.February.2024 18:51:51
--

open IO

def replicateM : Nat → IO α → IO (List α)
| 0, _     => return []
| k + 1, f => return (←f) :: (←replicateM k f)

def getLine : IO String := do return (←(←getStdin).getLine).trim
def readLn : IO Nat := do return (←getLine).toNat!

def List.removeEvery {α : Type} (xs : List α) (N : Nat) (i : Nat := 1) : List α :=
match xs with
| []     => []
| x::xs  =>
  if i = N then xs.removeEvery N
  else x :: xs.removeEvery N (i+1)

def main : IO Unit := do
  let K ← readLn
  let m ← readLn
  let ps ← replicateM m readLn
  let xs := Nat.succ <$> List.range K
  let ans := ps.foldl List.removeEvery xs
  ans.forM println
