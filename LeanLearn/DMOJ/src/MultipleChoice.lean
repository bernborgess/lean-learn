--
--    author:  bernborgess
--    problem: MultipleChoice - lean-learn
--    created: 05.February.2024 01:16:24
--

def replicateM (n : Nat) (f : IO α) : IO (List α) := match n with
| 0     => return []
| k + 1 => return (←f) :: (←replicateM k f)

def readLn : IO Nat := do return (←(←IO.getStdin).getLine).trim.toNat!
def getLine : IO String := do return ←(←IO.getStdin).getLine
def cmp (x:String) (y:String) := if x == y then 1 else 0

def main : IO Unit := do
    let n ← readLn
    let chk ← replicateM n getLine
    let ans ← replicateM n getLine
    let k := chk.zipWith cmp ans
    let w := k.foldl HAdd.hAdd 0
    IO.println w
