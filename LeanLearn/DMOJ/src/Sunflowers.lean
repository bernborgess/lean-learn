--
--    author:  bernborgess
--    problem: Sunflowers - lean-learn
--    created: 28.February.2024 08:22:56
--

open IO

def replicateM : Nat → IO α → IO (List α)
| 0, _     => return []
| k + 1, f => return (←f) :: (←replicateM k f)

def getLine : IO String := do return (←(←getStdin).getLine).trim
def readLn : IO Nat := do return (←getLine).toNat!
def getList : IO (List Int) := return ((←getLine).split Char.isWhitespace).map String.toInt!
def printList [ToString α] : List α → IO Unit := println ∘ String.join ∘ List.intersperse " " ∘ List.map toString

def List.transpose (l : List (List α)) : List (List α) := (l.foldr go #[]).toList where
  pop (old : List α) : StateM (List α) (List α)
    | [] => (old, [])
    | a :: l => (a :: old, l)
  go (l : List α) (acc : Array (List α)) : Array (List α) :=
    let (acc, l) := acc.mapM pop l
    l.foldl (init := acc) fun arr a => arr.push [a]

def List.rotate : List (List α) → List (List α) :=
  List.reverse ∘ List.transpose

def isSorted (xs : List Int) : Bool := List.and (xs.zipWith (·<=·) xs.tail!)

partial def find (G : List (List Int)) : List (List Int) :=
  if (G.map isSorted).and && (G.transpose.map isSorted).and then G
  else find G.rotate

def main : IO Unit := do
  let N ← readLn
  let G ← replicateM N getList
  let M := find G
  M.forM printList
