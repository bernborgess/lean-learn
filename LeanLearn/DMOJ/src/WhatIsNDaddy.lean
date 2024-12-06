--
--    author:  bernborgess
--    problem: WhatIsNDaddy - lean-learn
--    created: 14.February.2024 21:36:39
--

open IO List

def getLine : IO String := do return (←(←getStdin).getLine).trim

def readLn : IO Int := do return (←getLine).toInt!

def dad (n : Int) := (7 - abs (n - 5)) / 2
  where abs := Int.ofNat ∘ Int.natAbs

def main : IO Unit := readLn >>= println ∘ dad
