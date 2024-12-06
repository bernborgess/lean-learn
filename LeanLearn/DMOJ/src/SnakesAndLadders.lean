--
--    author:  bernborgess
--    problem: SnakesAndLadders - lean-learn
--    created: 25.February.2024 09:43:36
--

open IO

def getLine : IO String := do return (←(←getStdin).getLine).trim
def readLn : IO Nat := do return (←getLine).toNat!

def slide (x : Nat) : Nat :=
  [ (54,19),(90,48),(99,77),(9,34),(40,64),(67,86)]
   |>.lookup x |>.getD x

def log (s : Nat) := println s!"You are now on square {s}"

partial def play (s : Nat) : IO Nat := do
  let die ← readLn

  if die = 0 then
    println "You Quit!"
    return 0
  else
  let s' := s + die

  if s' > 100 then
    log s ; play s
  else

  let s'' := slide s'
  log s''

  if s'' = 100 then
    println "You Win!"
    return 100
  else
    play s''


def main : IO Unit := do
  _ ← play 1
