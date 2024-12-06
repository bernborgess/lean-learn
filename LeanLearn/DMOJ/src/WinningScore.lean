--
--    author:  bernborgess
--    problem: WinningScore - lean-learn
--    created: 05.February.2024 00:07:34
--

def readLn : IO Int := do
    let stdin ← IO.getStdin
    let i ← stdin.getLine
    match i.trim.toInt? with
    | none => return 0
    | some i => return i

open Ordering

def main : IO Unit := do
    let sa := (←readLn)*3 + (←readLn)*2 + (←readLn)
    let sb := (←readLn)*3 + (←readLn)*2 + (←readLn)
    let ans := match compare (sb-sa) 0 with
    | lt => "A"
    | eq => "T"
    | gt => "B"
    IO.println ans
