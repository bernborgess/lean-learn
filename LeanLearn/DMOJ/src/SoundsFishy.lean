--
--    author:  bernborgess
--    problem: SoundsFishy - lean-learn
--    created: 12.February.2024 18:42:35
--

open IO

def replicateM : Nat → IO α → IO (List α)
| 0, _     => return []
| k + 1, f => return (←f) :: (←replicateM k f)

def getLine : IO String := do return (←(←getStdin).getLine).trim

def readLn : IO Nat := do return (←getLine).toNat!

def uncurry (f : α → β → γ) (p : α × β) : γ :=
  f (p.fst) (p.snd)

def scan (f : Nat → Nat → Bool) (xs : List Nat) :=
  let ks := xs.zip xs.tail!
  ks.all (uncurry f)

def main : IO Unit := do
  let xs ← replicateM 4 readLn

  if scan (·>·) xs then
    println "Fish Diving"
  else if scan (·<·) xs then
    println "Fish Rising"
  else if scan (·==·) xs then
    println "Fish At Constant Depth"
  else
    println "No Fish"
