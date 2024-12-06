--
--    author:  bernborgess
--    problem: BodyMassIndex - lean-learn
--    created: 11.February.2024 23:04:23
--
import Lean.Data.Json.Parser

open IO

def readFloat : IO Float := do
  let s ← (←getStdin).getLine
  match Lean.Json.parse s with
  | .ok (.num t) => pure t.toFloat
  | _ => pure 1.0

def main : IO Unit := do
  let weight ← readFloat
  let height ← readFloat
  let bmi := weight / (height * height)
  let msg := if bmi > 25          then "Overweight"
             else if bmi > 18.5   then "Normal weight"
             else                      "Underweight"
  println msg
