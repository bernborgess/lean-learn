--
--    author:  bernborgess
--    problem: Uncrackable - lean-learn
--    created: 06.March.2024 21:33:15
--

open IO

def getLine : IO String := do return (←(←getStdin).getLine).trim

def List.count {α : Type} (p : α → Bool) (l : List α) : Nat := go 0 l
  where go
  | n,[]      => n
  | n,(x::xs) => if p x then go (n+1) xs else go n xs

def main : IO Unit := do
  let s := (←getLine).toList
  if 8 <= s.length ∧ s.length <= 12
      ∧ s.count Char.isLower >= 3
      ∧ s.count Char.isUpper >= 2
      ∧ s.count Char.isDigit >= 1 then
    println "Valid"
  else
    println "Invalid"
