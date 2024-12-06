--
--    author:  bernborgess
--    problem: AmeriCanadian - lean-learn
--    created: 19.February.2024 19:50:41
--

open IO String List
def getLine : IO String := do return (←(←getStdin).getLine).trim

def toCanada -- 🍁
| 'r'::'o'::c::l::r =>
  if "bcdfghjklmnpqrstvwxz".toList.contains c then
    'r'::'u'::'o'::c::l::r
  else
    'r'::'o'::c::l::r
| s => s

partial def main2 : IO Unit := do
  let line ← getLine
  if line != "quit!" then
    println ∘ mk ∘ reverse ∘ toCanada ∘ reverse ∘ toList $ line
    main2
