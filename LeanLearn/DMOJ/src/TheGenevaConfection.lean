--
--    author:  bernborgess
--    problem: TheGenevaConfection - lean-learn
--    created: 28.February.2024 10:45:23
--

open IO

def replicateM : Nat → IO α → IO (List α)
| 0, _     => return []
| k + 1, f => return (←f) :: (←replicateM k f)

def replicateM_ : Nat → IO Unit → IO Unit
| 0, _     => return
| k + 1, f => do f; replicateM_ k f

def getLine : IO String := do return (←(←getStdin).getLine).trim
def readLn : IO Nat := do return (←getLine).toNat!

def possible : Nat → List Nat → List Nat → Bool
| _, [], []    => true
| n, [], y::ys => if n==y then possible (n+1) [] ys else false
| n, x::xs, ys =>
  if n == x then possible (n+1) xs ys
  else match ys with
  | []    => possible n xs [x]
  | y::ys =>
    if n == y then possible (n+1) (x::xs) ys
    else possible n xs (x::y::ys)

def main : IO Unit := do
  let T ← readLn
  replicateM_ T $ do
    let N ← readLn
    let xs ← replicateM N readLn
    println $ cond (possible 1 xs.reverse []) "Y" "N"
