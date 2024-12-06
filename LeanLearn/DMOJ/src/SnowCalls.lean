--
--    author:  bernborgess
--    problem: SnowCalls - lean-learn
--    created: 07.March.2024 22:36:43
--

open IO List

def replicateM_ : Nat → IO Unit → IO Unit
| 0, _     => return
| k + 1, f => do f; replicateM_ k f

def getLine : IO String := do return (←(←getStdin).getLine).trim
def readLn : IO Nat := do return (←getLine).toNat!

def toDig (ch : Char) : Char := ks.find? (· |>.fst.contains ch) |>.getD ("",ch) |>.snd
  where ks := [  ("ABC",'2'), ("DEF",'3'),
    ("GHI",'4'), ("JKL",'5'), ("MNO",'6'),
    ("PQRS",'7'),("TUV",'8'), ("WXYZ",'9') ]

def main : IO Unit := do
  let t ← readLn
  replicateM_ t $ do
    let line ← getLine
    let k := map toDig $ take 10 $ line.toList.filter Char.isAlphanum
    println $ String.mk $
      (λ | [a,b,c,d,e,f,g,h,i,j] => [a,b,c,'-',d,e,f,'-',g,h,i,j]
         | l => l) k
