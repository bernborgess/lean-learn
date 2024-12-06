--
--    author:  bernborgess
--    problem: SpecialDay - lean-learn
--    created: 04.February.2024 21:21:54
--

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

def main : IO Unit := do
    let month ← readLn
    let day   ← readLn

    match bas month 2 with
    | "Special" => IO.println $ bas day 18
    | s         => IO.println s
