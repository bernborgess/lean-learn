--
--    author:  bernborgess
--    problem: WhoisintheMiddle - loja
--    created: 04.February.2024 20:00:29
--
-----------------------------------------------------

def replicateM (n : Nat) (f : IO α) : IO (List α) :=
  match n with
  | 0 => return []
  | (k + 1) => do
    let x ← f;
    let xs ← replicateM k f
    return xs.cons x

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

----------------------------------------------------------------


def main : IO Unit := do
  let xs ← replicateM 3 readLn
  let mid : Option Nat := do
    guard (xs.length == 3)
    let M ← xs.maximum?
    let m ← xs.minimum?
    let k := flip List.erase m $ xs.erase M
    k.head?

  match mid with
  | some x  => IO.println x
  | none    => return
