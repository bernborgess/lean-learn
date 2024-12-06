--
--    author:  bernborgess
--    problem: EnglishOrFrench - lean-learn
--    created: 10.February.2024 22:28:42
--

open IO

def replicateM : Nat → IO α → IO (List α)
| 0, _     => return []
| k + 1, f => return (←f) :: (←replicateM k f)

def readLn : IO Nat := do return (←(←IO.getStdin).getLine).trim.toNat!

def main : IO Unit := do
  let N ← readLn
  let txt ← String.join <$> replicateM N (←getStdin).getLine

  let score | 't' => 1 | 'T' => 1 | 's' => -1 | 'S' => -1 | _ => 0
  let k : Int := txt.foldl (λ acc ch => acc + score ch) 0

  if k > 0 then
    println "English"
  else
    println "French"
