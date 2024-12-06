--
--    author:  bernborgess
--    problem: FederalVotingAge - lean-learn
--    created: 06.March.2024 10:20:25
--

open IO

def replicateM_ : Nat → IO Unit → IO Unit
| 0, _     => return
| k + 1, f => do f; replicateM_ k f

def getLine : IO String := do return (←(←getStdin).getLine).trim
def readLn : IO Nat := do return (←getLine).toNat!

def getTuple : IO (Int × Int × Int) := do
  let k := (←getLine).split Char.isWhitespace
  return ((k.get! 0).toNat!,(k.get! 1).toNat!,(k.get! 2).toNat!)

def main : IO Unit := do
  let n ← readLn
  replicateM_ n $ do
    let (y,m,d) ← getTuple
    if y < 1989 ∨ y = 1989 ∧ (m < 2 ∨ m = 2 ∧ d <= 27) then
      println "Yes"
    else
      println "No"
