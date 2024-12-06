--
--    author:  bernborgess
--    problem: DoTheShuffle - lean-learn
--    created: 23.February.2024 19:12:00
--

open IO

def getLine : IO String := do return (←(←getStdin).getLine).trim
def readLn : IO Nat := do return (←getLine).toNat!

def printList [ToString α] : List α → IO Unit := println ∘ String.join ∘ List.intersperse " " ∘ List.map toString

-- | Apply a function @n@ times to a given value.
def nTimes : Nat → (a → a) → (a → a)
| 0,  _ => id
| 1,  f => f
| n+1,f => f ∘ nTimes n f

abbrev Track := List Char

def buttons : List (Track → Track) := [ id,
  λ | [a,b,c,d,e] => [b,c,d,e,a] | _ => [],
  λ | [a,b,c,d,e] => [e,a,b,c,d] | _ => [],
  λ | [a,b,c,d,e] => [b,a,c,d,e] | _ => [],
]

partial def play (t :Track) : IO Track := do
  let b ← readLn
  let n ← readLn
  if b = 4 then pure t else
  play $ nTimes n (buttons.get! b) t

def main : IO Unit := do
  let final ← play ['A','B','C','D','E']
  printList final
