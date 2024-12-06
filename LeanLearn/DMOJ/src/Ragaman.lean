--
--    author:  bernborgess
--    problem: Ragaman - lean-learn
--    created: 06.March.2024 15:18:19
--

open IO

def getLine : IO String := do return (←(←getStdin).getLine).trim

def List.sort [LT α] [DecidableRel ((·<·) : α → α → Prop)] : List α → List α :=
  Array.toList ∘ flip Array.qsort (·<·) ∘ Array.mk

def getDict : IO (List (Char × Nat)) := do
  let groups := (←getLine).toList.sort.groupBy (·=·)
  let tokens := groups.map (λ xs => (xs.head!,xs.length) )
  return tokens.filter (·.fst != '*')

def main : IO Unit := do
  let word ← getDict
  let anag ← getDict
  let k := anag.all (λ (c,n) => (word.lookup c).getD 0 >= n)
  println $ if k then "A" else "N"
