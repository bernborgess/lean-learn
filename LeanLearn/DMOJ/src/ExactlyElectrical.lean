--
--    author:  bernborgess
--    problem: ExactlyElectrical - lean-learn
--    created: 05.March.2024 19:05:39
--

open IO

def getLine : IO String := do return (←(←getStdin).getLine).trim
def readLn : IO Nat := do return (←getLine).toNat!
def getList : IO (List Int) := return ((←getLine).split Char.isWhitespace).map String.toInt!

def getTuple : IO (Int × Int) := do
  let xs ← getList
  return (xs.head!, xs.tail!.head!)

def main : IO Unit := do
  let (a,b) ← getTuple
  let (c,d) ← getTuple
  let t ← readLn
  let x := (a - c).natAbs
  let y := (b - d).natAbs
  let k := x + y
  println $ if k <= t ∧ k % 2 = t % 2 then "Y" else "N"
