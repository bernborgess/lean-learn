--
--    author:  bernborgess
--    problem: ReturningHome - lean-learn
--    created: 05.March.2024 17:11:19
--

open IO

def getLine : IO String := do return (←(←getStdin).getLine).trim

partial def walk (ps ds : List String) : IO (List String × List String) := do
  let d ← getLine
  let p ← getLine
  if p == "SCHOOL" then
    return (ps,d::ds)
  else
    walk (p::ps) (d::ds)

def speak | "L" => "RIGHT" | _ => "LEFT"

def main : IO Unit := do
  let (ps,ds) ← walk ["HOME"] []
  (ps.zip ds).forM $ λ (p,d) ↦
    if p = "HOME" then
      println s!"Turn {speak d} into your HOME."
    else
      println s!"Turn {speak d} onto {p} street."
