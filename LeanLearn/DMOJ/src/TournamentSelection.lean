--
--    author:  bernborgess
--    problem: TournamentSelection - lean-learn
--    created: 12.February.2024 18:07:03
--

open IO List

def replicateM : Nat → IO α → IO (List α)
| 0, _     => return []
| k + 1, f => return (←f) :: (←replicateM k f)

def getLine : IO String := do return (←(←getStdin).getLine).trim

def getChar : IO Char := do return head! ∘ String.toList $ (←getLine)

def group k :=
  if k >= 5 then 1
  else if k >= 3 then 2
  else if k >= 1 then 3
  else -1

def main := replicateM 6 getChar >>= println ∘ group ∘ length ∘ filter (·=='W')
