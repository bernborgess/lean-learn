--
--    author:  bernborgess
--    problem: BabblingBrooks - lean-learn
--    created: 02.March.2024 16:27:57
--

open IO

def replicateM : Nat → IO α → IO (List α)
| 0, _     => return []
| k + 1, f => return (←f) :: (←replicateM k f)

def getLine : IO String := do return (←(←getStdin).getLine).trim
def readLn : IO Nat := do return (←getLine).toNat!
def printList [ToString α] : List α → IO Unit := println ∘ String.join ∘ List.intersperse " " ∘ List.map toString

def split : Nat → Float → List Float → List Float
| 1,p,(x::xs) => (x*p)/100.0 :: (x*(100-p))/100.0 :: xs
| i,p,(x::xs) => x :: split (i-1) p xs
| _,_,_       => []

def join : Nat → List Float → List Float
| 1,(x::y::xs) => (x+y) :: xs
| i,(x::xs)    => x :: join (i-1) xs
| _,_          => []

partial def proceed (flows : List Float) : IO (List Float) := do
  let op ← readLn
  match op with
  | 99 => do -- split
    let i ← readLn
    let flow ← readLn
    proceed $ split i flow.toFloat flows
  | 88 => do -- join
    let i ← readLn
    proceed $ join i flows
  | _  => return flows

def main : IO Unit := do
  let n ← readLn
  let flows ← replicateM n readLn
  let flows ← proceed (flows.map Nat.toFloat)
  printList $ flows.map (·.round)
