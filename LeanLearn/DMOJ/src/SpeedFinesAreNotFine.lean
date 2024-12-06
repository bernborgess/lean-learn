--
--    author:  bernborgess
--    problem: SpeedFinesAreNotFine - lean-learn
--    created: 10.February.2024 22:13:49
--

open IO

def readLn : IO Nat := do return (←(←getStdin).getLine).trim.toNat!

def main : IO Unit := do
  let lim ← readLn
  let car ← readLn
  let x := car - lim
  if x == 0 then
    println "Congratulations, you are within the speed limit!"
  else
    let fine :=
      if x <= 20 then 100
      else if x <= 30 then 270
      else 500
    println s!"You are speeding and your fine is ${fine}."
