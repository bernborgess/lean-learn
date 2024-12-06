--
--    author:  bernborgess
--    problem: SmileWithSimiles - lean-learn
--    created: 15.February.2024 18:25:43
--

open IO

def replicateM : Nat → IO α → IO (List α)
| 0, _     => return []
| k + 1, f => return (←f) :: (←replicateM k f)

def getLine : IO String := do return (←(←getStdin).getLine).trim
def readLn : IO Nat := do return (←getLine).toNat!

instance : Monad List where
  pure := List.pure
  bind := List.bind

def main : IO Unit := do
  let n ← readLn
  let m ← readLn

  let ads ← replicateM n getLine
  let nos ← replicateM m getLine

  let ans := do
    let ad ← ads
    let no ← nos
    return s!"{ad} as {no}"

  ans.forM println
