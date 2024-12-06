--
--    author:  bernborgess
--    problem: SecretInstructions - lean-learn
--    created: 04.March.2024 00:39:40
--

open IO

def getLine : IO String := do return (←(←getStdin).getLine).trim
def Char.toNat! := String.toNat! ∘ Char.toString

def splitter : List Char → Nat × String
| [v,w,x,y,z] =>
  let sm := v.toNat! + w.toNat!
  let mv := (String.mk [x,y,z])
  (sm,mv)
| _           => (0,"")

def zeigen : Fin 2 → String → IO Unit
| 0,mv => println s!"left {mv}"
| 1,mv => println s!"right {mv}"

partial def move (dir : Fin 2) : IO (Fin 2) := do
  let line ← getLine
  if line.length ≠ 5 ∨ line = "99999" then return 0 else
  let (sm,mv) := splitter line.toList
  if sm = 0 then            zeigen dir mv; move dir
  else if sm % 2 = 0 then   zeigen 1 mv; move 1
  else                      zeigen 0 mv; move 0

def main : IO Unit := do
  let _ ← move 0
