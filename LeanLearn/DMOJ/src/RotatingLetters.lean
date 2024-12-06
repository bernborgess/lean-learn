--
--    author:  bernborgess
--    problem: RotatingLetters - lean-learn
--    created: 12.February.2024 17:58:18
--

open IO

def getList : IO (List Char) := return ((←(←getStdin).getLine).trim).toList

def isRot := "IOSHZXN".contains

def main : IO Unit := do
  let line ← getList
  println $ if line.all isRot then "YES" else "NO"
