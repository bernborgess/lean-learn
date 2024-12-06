--
--    author:  bernborgess
--    problem: Trik - lean-learn
--    created: 04.March.2024 10:09:13
--

open IO

def getLine : IO String := do return (←(←getStdin).getLine).trim

abbrev F3 := Fin 3

/-- Swap the factors of a product. `swap (a, b) = (b, a)` -/
def Prod.swap : α × β → β × α := fun p ↦ (p.2, p.1)
def List.swap : List (α × β) → List (β × α) := List.map Prod.swap

def swaps (moves : List (F3 × F3)) (x : F3) : F3 :=
  moves ++ moves.swap |>.lookup x |>.getD x

def move : F3 → Char → F3
| x,'A' => swaps [(0,1)] x
| x,'B' => swaps [(1,2)] x
| x,'C' => swaps [(0,2)] x
| x, _  => x

def main : IO Unit := do
  let moves ← getLine
  let k := moves.foldl move 0
  println $ k.val + 1
