--
--    author:  bernborgess
--    problem: Telemarketer - lean-learn
--    created: 05.February.2024 00:26:59
--

def replicateM (n : Nat) (f : IO α) : IO (List α) := match n with
| 0     => return []
| k + 1 => return (←f) :: (←replicateM k f)

def readLn : IO Nat := do return (←(←IO.getStdin).getLine).trim.toNat!

def is98 (n : Nat) := n == 9 || n == 8

def main : IO Unit := do
    let xs ← replicateM 4 readLn
    match xs with
    | [w,x,y,z] => do
        let ans := if is98 w && x == y && is98 z
        then "ignore" else "answer"
        IO.println ans
    | _ => return
