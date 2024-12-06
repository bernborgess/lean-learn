--
--    author:  bernborgess
--    problem: CyclicShifts - lean-learn
--    created: 06.March.2024 22:23:15
--

open IO

def getList : IO (List Char) := do return (←(←getStdin).getLine).trim.toList

namespace List

def splitAt (n : Nat) (l : List α) : List α × List α := go l n #[] where
  go : List α → Nat → Array α → List α × List α
  | [], _, _ => (l, [])
  | x :: xs, n+1, acc => go xs n (acc.push x)
  | xs, _, acc => (acc.toList, xs)

def rotate (l : List α) (n : Nat) : List α :=
  let (l₁, l₂) := List.splitAt (n % l.length) l
  l₂ ++ l₁

def rotations (l : List α) : List (List α) :=
  let is := List.range l.length
  is.map (l.rotate ·)

def tails : List α → List (List α)
  | [] => [[]]
  | a :: l => (a :: l) :: tails l

def isInfixOf [BEq α] (needle haystack : List α) : Bool :=
  haystack.tails.any (needle.isPrefixOf ·)

end List

def main : IO Unit := do
  let T ← getList
  let S ← getList
  let b := S.rotations.any λ xs ↦ xs.isInfixOf T
  println $ cond b "yes" "no"
