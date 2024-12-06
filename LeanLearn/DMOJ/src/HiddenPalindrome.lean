--
--    author:  bernborgess
--    problem: HiddenPalindrome - lean-learn
--    created: 01.March.2024 14:17:39
--

open IO

def getLine : IO String := do return (←(←getStdin).getLine).trim

partial def spread (s : List Char) (l r : Int) :=
  if l < 0 ∨ r >= s.length then                     0
  else if l = r then                                1 + rc
  else if (s.get! l.toNat) = (s.get! r.toNat) then  2 + rc
  else                                              0
  where
    rc := spread s (l-1) (r+1)

def main : IO Unit := do
  let s ← getLine
  let r := List.map Int.ofNat $ List.range s.length
  let a := r.map (λ i ↦ spread s.toList i i) ++
           r.map (λ i ↦ spread s.toList i (i+1))
  println $ a.foldl max 1
