--
--    author:  bernborgess
--    problem: Rovarspraket - lean-learn
--    created: 07.March.2024 19:04:38
--

open IO

def getLine : IO String := do return (←(←getStdin).getLine).trim

namespace Char

def consonants := "bcdfghjklmnpqrstvwxyz"

def isConsonant := (consonants.contains ·)

def closestVowel (ch : Char) :=
  if ch > 'r' then 'u'
  else if ch > 'l' then 'o'
  else if ch > 'g' then 'i'
  else if ch > 'c' then 'e'
  else 'a'

def nextConsonant (ch : Char) := (consonants.toList.find? (λ k ↦ k > ch)).getD 'z'

end Char

def rovar (ch : Char ) : List Char :=
  if ch.isConsonant
  then [ch,ch.closestVowel,ch.nextConsonant]
  else [ch]

def main : IO Unit := do
  let word ← getLine
  let k := String.mk (word.toList.map rovar).join
  println k
