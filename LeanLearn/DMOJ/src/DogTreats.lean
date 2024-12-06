--
--    author:  bernborgess
--    problem: DogTreats - lean-learn
--    created: 15.February.2024 17:40:07
--

open IO

def getLine : IO String := do return (←(←getStdin).getLine).trim

def readLn : IO Nat := do return (←getLine).toNat!


def main : IO Unit := do
  let S ← readLn
  let M ← readLn
  let L ← readLn
  if S + 2*M + 3*L >= 10 then
    println "happy"
  else
    println "sad"
