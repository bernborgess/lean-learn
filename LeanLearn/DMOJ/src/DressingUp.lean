--
--    author:  bernborgess
--    problem: DressingUp - lean-learn
--    created: 27.February.2024 22:04:40
--

open IO List

def getLine : IO String := do return (←(←getStdin).getLine).trim
def readLn : IO Nat := do return (←getLine).toNat!

def pyramid : Nat → List Nat
| 0 => [0] | 1 => [1]
| n + 2 => [1] ++ ((pyramid n).map (2+·)) ++ [1]

def tie (H i : Nat) : String :=
  let ls := replicate i '*' ++ replicate (H - i) ' '
  String.mk (ls ++ ls.reverse)

def main : IO Unit := do
  let H ← readLn
  let is := pyramid H
  (is.map $ tie H).forM println
