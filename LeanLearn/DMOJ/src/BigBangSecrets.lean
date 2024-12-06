--
--    author:  bernborgess
--    problem: BigBangSecrets - lean-learn
--    created: 04.March.2024 21:39:26
--

open IO

def getLine : IO String := do return (←(←getStdin).getLine).trim
def readLn : IO Nat := do return (←getLine).toNat!

theorem gtz_26 : 26 > 0 := by exact Nat.succ_pos 25

abbrev ABC := Fin 26

def Nat.toABC := (Fin.ofNat' · gtz_26)

def Char.toFin (ch : Char) : ABC := (ch.toNat - 'A'.toNat).toABC

def main : IO Unit := do
  let K ← readLn
  let word ← getLine
  let decode | (i, ch) => ch.toFin - 3 * i.toABC - K.toABC
  let k := (word.toList.enumFrom 1).map decode
  k.forM $ print ∘ Char.ofNat ∘ (·.val + 'A'.toNat)
