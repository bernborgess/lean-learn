--
--    author:  bernborgess
--    problem: TimeToDecompress - lean-learn
--    created: 23.February.2024 20:44:16
--

open IO

def replicateM_ : Nat → IO Unit → IO Unit
| 0, _       => return
| (k + 1), f => do f; replicateM_ k f

def getLine : IO String := do return (←(←getStdin).getLine).trim
def readLn : IO Nat := do return (←getLine).toNat!

def decode : IO Unit := do
  let line ← flip String.split Char.isWhitespace <$> getLine
  let N := (line.get! 0).toNat!
  let x := line.get! 1
  println $ String.join $ List.replicate N x

def main : IO Unit := do
  let L ← readLn
  replicateM_ L decode
