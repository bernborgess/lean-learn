--
--    author:  bernborgess
--    problem: ISBN - lean-learn
--    created: 20.February.2024 11:06:42
--

open IO String

def replicateM : Nat → IO α → IO (List α)
| 0, _     => return []
| k + 1, f => return (←f) :: (←replicateM k f)

def getLine : IO String := do return (←(←getStdin).getLine).trim
def readChar (ch : Char) := Char.toNat ch - Char.toNat '0'

def agg
| (s,1), ch => (s + readChar ch,    3)
| (s,3), ch => (s + 3 * readChar ch,1)
| _, _      => (0,0)

def main : IO Unit := do
  let ns ← replicateM 3 getLine
  let str := append "9780921418" $ join $ ns
  let (s,_) := str.foldl agg (0,1)
  println s!"The 1-3-sum is {s}"
