--
--    author:  bernborgess
--    problem: ColdCompress - lean-learn
--    created: 25.February.2024 10:59:02
--

open IO

def replicateM_ : Nat → IO Unit → IO Unit
| 0, _     => return
| k + 1, f => do f; replicateM_ k f

def getLine : IO String := do return (←(←getStdin).getLine).trim
def readLn : IO Nat := do return (←getLine).toNat!

def encrypt : IO Unit := do
  let line ← getLine
  let gps := line.toList.groupBy (·==·)
  gps.forM λ xs => do print s!"{xs.length} {xs.head!} "
  println ""

def main : IO Unit := do
  let N ← readLn
  replicateM_ N encrypt
