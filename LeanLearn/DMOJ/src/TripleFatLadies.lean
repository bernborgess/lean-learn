--
--    author:  bernborgess
--    problem: tripleFatLadies - loja
--    created: 08.November.2023 19:10:32
--

def replicateM_ (n : Nat) (f : IO Unit) : IO Unit :=
  match n with
  | 0 => return
  | (k + 1) => do f; replicateM_ k f

def readLn : IO Nat := do
  let stdin ← IO.getStdin
  let i ← stdin.getLine
  match i.trim.toNat? with
    | none => return 0
    | some i => return i

def getList : IO (List Int) := do
  let stdin ← IO.getStdin
  let line ← stdin.getLine
  let k := line.trim.split Char.isWhitespace
  return List.map String.toInt! k

------------------------------------------

def cubeEnds888 (n : Nat) :=
  false

def next888 (n : Nat) :=
  if cubeEnds888 n then n
  else next888 (n + 1)




def main : IO Unit := do
  let t ← readLn
  replicateM_ t $ do
    let k ← readLn
    IO.println $ next888 k
