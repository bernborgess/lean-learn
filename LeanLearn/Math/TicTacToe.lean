--
--    author:  bernborgess
--    problem: TicTacToe - lean-learn
--    created: 22.February.2024 19:24:57
--

open IO
def getLine : IO String := do return (←(←getStdin).getLine).trim

def play (jog : String) : Option String := match jog with
| "pedra" => some "papel"
| "papel" => some "tesoura"
| "tesoura" => some "pedra"
| _ => none

def main : IO Unit := do
  let jog ← getLine
  let rob := play jog
  match rob with
  | none    => println "Jogou errado"
  | some r  => println s!"Eu jogo {r}! \nGanhei!"
