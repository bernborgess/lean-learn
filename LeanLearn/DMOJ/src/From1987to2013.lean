--
--    author:  bernborgess
--    problem: From1987to2013 - lean-learn
--    created: 15.February.2024 18:39:53
--

open IO

def replicateM : Nat → IO α → IO (List α)
| 0, _     => return []
| k + 1, f => return (←f) :: (←replicateM k f)

def replicateM_ : Nat → IO Unit → IO Unit
| 0, _       => return
| (k + 1), f => do f; replicateM_ k f

def getLine : IO String := do return (←(←getStdin).getLine).trim

def readLn : IO Nat := do return (←getLine).toNat!

def getList : IO (List Int) := return ((←getLine).split Char.isWhitespace).map String.toInt!

def main : IO Unit := do
  let num ← getLine

  println "Hello World!"
