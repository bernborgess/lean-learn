--
--    author:  bernborgess
--    problem: Boolean - lean-learn
--    created: 05.March.2024 19:43:04
--

open IO

def getLine : IO String := do return (←(←getStdin).getLine).trim
def getList : IO (List String) := return ((←getLine).split Char.isWhitespace)

def reduce
| "True",n => n % 2 == 0
| _,     n => n % 2 == 1

def main : IO Unit := do
  let xs ← getList
  let b := xs.reverse.head!
  let n := xs.length - 1
  println $ if reduce b n then "True" else "False"
