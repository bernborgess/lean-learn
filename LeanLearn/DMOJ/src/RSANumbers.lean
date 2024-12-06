--
--    author:  bernborgess
--    problem: RSANumbers - lean-learn
--    created: 26.February.2024 11:02:24
--

open IO List

def getLine : IO String := do return (←(←getStdin).getLine).trim
def readLn : IO Nat := do return (←getLine).toNat!

def sort [LT α] [DecidableRel ((·<·) : α → α → Prop)] : List α → List α :=
  Array.toList ∘ flip Array.qsort (·<·) ∘ Array.mk

def fromTo (l r : Nat) : List Nat := map (·+l) $ range (r-l+1)

partial def primes : List Nat := go (fromTo 2 1000)
  where
    go : List Nat → List Nat
    | [] => []
    | p :: xs => p :: go (xs.filter  (· % p != 0))

partial def factors : Nat → List Nat := go primes
  where
    go : List Nat → Nat → List Nat
    | _,     1 => []
    | [],    _ => []
    | p::ps, n =>
      if n % p == 0 then p :: (go (p::ps) (n/p))
      else go ps n

def divisors := foldl (·*·) 1 ∘ map (1 + length ·) ∘ groupBy (·=·) ∘ sort ∘ factors

def main : IO Unit := do
  let l ← readLn
  let r ← readLn
  let xs := fromTo l r
  let ans := length $ filter (·=4) $ xs.map divisors
  println s!"The number of RSA numbers between {l} and {r} is {ans}"
