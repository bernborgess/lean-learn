--
--    author:  bernborgess
--    problem: ZeroThatOut - lean-learn
--    created: 19.February.2024 11:20:54
--

open IO

def replicateM : Nat → IO α → IO (List α)
| 0, _     => return []
| k + 1, f => return (←f) :: (←replicateM k f)

def getLine : IO String := do return (←(←getStdin).getLine).trim
def readLn : IO Nat := do return (←getLine).toNat!

def zeroThat
| (_ :: xs), 0 => xs
| xs, k => k :: xs

def main : IO Unit := do
  let K ← readLn
  let xs ← replicateM K readLn
  let k := xs.foldl zeroThat []
  println $ k.foldr (·+·) 0
