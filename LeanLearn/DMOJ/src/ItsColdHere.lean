--
--    author:  bernborgess
--    problem: ItsColdHere - lean-learn
--    created: 04.April.2024 20:10:37
--

open IO

def getLine : IO String := do return (←(←getStdin).getLine).trim

abbrev CT := String × Int

def parseCity (s : String) : CT :=
  let toks := s.split Char.isWhitespace
  match toks with
  | [city,stemp] => (city,stemp.toInt!)
  | _ => ("",0)

partial def getCities (bf : CT): IO CT := do
  let line ← getLine
  if line.length = 0 then return bf else
  let af := parseCity line
  getCities (if af.2 < bf.2 then af else bf)

def main : IO Unit := do
  let (city,_) ← getCities ("",300)
  println s!"{city}"
