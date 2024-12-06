--
--    author:  bernborgess
--    problem: CCC13J1Nextinline - loja
--    created: 14.November.2023 14:49:29
--

def readLn : IO Nat := do
  let stdin ← IO.getStdin
  let i ← stdin.getLine
  match i.trim.toNat? with
    | none => return 0
    | some i => return i

def main : IO Unit := do
  let y ← readLn
  let m ← readLn
  IO.println (m+m-y)
