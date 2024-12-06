--
--    author:  bernborgess
--    problem: PrettyAveragePrimes - lean-learn
--    created: 05.March.2024 19:49:30
--

open IO List

def getLine : IO String := do return (←(←getStdin).getLine).trim
def readLn : IO Nat := do return (←getLine).toNat!

/-- Range with `[l,r)` -/
def fromTo (l r : Nat) : List Nat := List.map (·+l) $ List.range (r-l+1)

/-- Range with `[l,r)` step `s` -/
def fromToStep (l r s : Nat) : List Nat := map (·+l) $ map (·*s) $ range ((r-l+1)/s)

def LIM := 2000000

def sieve : IO (Array Bool) := do
  let mut p := Array.mk $ replicate (LIM+1) true
  p := p.set! 0 false
  p := p.set! 1 false
  for i in fromToStep 4 (LIM+1) 2 do
    p := p.set! i false
  let mut i := 3
  while i * i <= LIM + 1 do
    if p.get! i then
      for j in fromToStep (i*i) (LIM+1) (2*i) do
        p := p.set! j false
    i := i + 1
  return p

def main : IO Unit := do
  let T ← readLn
  let is_prime ← sieve
  for _ in range T do
    let N ← readLn
    for a in List.range N do
      if !is_prime.get! a then
        continue
      let b := 2 * N - a
      if !is_prime.get! b then
        continue
      println s!"{a} {b}"
      break
