--
--    author:  bernborgess
--    problem: 16bit
--    created: 08.November.2023 00:06:48
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


def main : IO Unit := do
  let n ← readLn
  replicateM_ n $ do
    let xs ← getList
    let b :=
      match xs with
        | [x,y,z] => x * y == z
        | _ => false
    IO.println $ bool "16 BIT S/W ONLY" "POSSIBLE DOUBLE SIGMA" b
