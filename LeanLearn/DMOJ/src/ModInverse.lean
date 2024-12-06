--
--    author:  bernborgess
--    problem: ModInverse - lean-learn
--    created: 03.March.2024 18:48:11
--

open IO

def getLine : IO String := do return (←(←getStdin).getLine).trim
def readLn : IO Nat := do return (←getLine).toNat!

partial def euclid (a b : Int) :=
  if b = 0 then (a,1,0)
  else
    let (g,x,y) := euclid b (a%b)
    (g, y, x-y*(a/b))

def inverse (a n : Int) :=
  let (g,r,_) := euclid a n
  match g with
  | 1 => some $ if r < 0 then r + n else r
  | _ => none

def main : IO Unit := do
  let x ← readLn
  let m ← readLn
  match inverse x m with
  | some x => println x
  | none   => println "No such integer exists."
