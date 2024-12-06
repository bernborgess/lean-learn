--
--    author:  bernborgess
--    problem: AlpacaShapes - lean-learn
--    created: 06.March.2024 10:15:52
--

open IO

def getLine : IO String := do return (←(←getStdin).getLine).trim

def getPair : IO (Float × Float) := do
  let k := (←getLine).split Char.isWhitespace
  return (k.head!.toNat!.toFloat,k.tail!.head!.toNat!.toFloat)

def main : IO Unit := do
  let (S,R) ← getPair
  if S^2 > 3.14 * R^2 then
    println "SQUARE"
  else
    println "CIRCLE"
