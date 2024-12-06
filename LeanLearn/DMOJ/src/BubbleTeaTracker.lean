--
--    author:  bernborgess
--    problem: bubbleTeaTracker - loja
--    created: 08.November.2023 20:26:39
--

def readLn : IO Nat := do
  let stdin ← IO.getStdin
  let i ← stdin.getLine
  match i.trim.toNat? with
    | none => return 0
    | some i => return i

------------------------------------------

def recur (i : Nat) (acc : Nat): IO Unit := do
  let x ← readLn
  if i > 0 then do
    IO.println (acc+x)
    recur (i-1) (acc+x)
  else
    return ()

def main : IO Unit := do
  let n ← readLn
  recur n 0
