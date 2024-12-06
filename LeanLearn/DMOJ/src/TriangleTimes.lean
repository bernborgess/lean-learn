--
--    author:  bernborgess
--    problem: TriangleTimes - lean-learn
--    created: 04.February.2024 21:21:54
--

def replicateM (n : Nat) (f : IO α) : IO (List α) :=
  match n with
  | 0 => return []
  | (k + 1) => do
    let x ← f;
    let xs ← replicateM k f
    return xs.cons x

def readLn : IO Nat := do
    let stdin ← IO.getStdin
    let i ← stdin.getLine
    match i.trim.toNat? with
    | none      => pure 0
    | some i    => pure i

def bas (x n: Nat) : String :=
    match compare x n with
    | Ordering.lt => "Before"
    | Ordering.eq => "Special"
    | Ordering.gt => "After"

open Ordering

def main : IO Unit := do
    let xs ← replicateM 3 readLn
    let sm := xs.foldl Nat.add 0
    let s := if sm != 180
        then "Error"
    else if xs.all (λ x => x == 60)
        then "Equilateral"
    else if xs.eraseDups.length == 2
        then "Isosceles"
    else "Scalene"

    IO.println s
