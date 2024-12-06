--
--    author:  bernborgess
--    problem: KnightHop - lean-learn
--    created: 05.March.2024 08:32:34
--

open IO List

def getLine : IO String := do return (←(←getStdin).getLine).trim

abbrev P2 := Int × Int

def getPair : IO P2 := do
  let k := (←getLine).split Char.isWhitespace
  return (k.head!.toNat!,k.tail!.head!.toNat!)

def negFst : P2 → List P2
| (x,y) => [(x,y),(-x,y)]

def negSnd : P2 → List P2
| (x,y) => [(x,y),(x,-y)]

-- map : (a → b) → List a → List b
-- join : List (List a) → List a
-- mapJoin : (a → List b) → List a → List b
-- bind : List α → (α → List β) → List β

def moves : List P2 :=
  List.bind (List.bind [(1,2),(2,1)] negFst) negSnd
  -- join $ map negSnd $ join $ map negFst [(1,2),(2,1)]
  -- ((([(1,2),(2,1)].map negFst).join).map negSnd).join

def inRange : P2 → Bool
| (x,y) => x > 0 ∧ x <= 8 ∧ y > 0 ∧ y <= 8

partial def main : IO Unit := do
  let start ← getPair
  let final ← getPair

  let rec search (walk : List (Nat × P2)) (visited : List P2) : Nat :=
    match walk with
    | []          => 0
    | ((d,p)::ws) =>
      if p = final then d
      else -- put in walk all neighbours of p that are not in visited
      let addP | (x,y) => (x+p.fst,y+p.snd)
      let unvisited := not ∘ visited.contains
      let dn := map (d+1,·) ∘ filter unvisited ∘ filter inRange ∘ map addP $ moves
      search (ws++dn) (p::visited)

  println $ search [(0,start)] []
