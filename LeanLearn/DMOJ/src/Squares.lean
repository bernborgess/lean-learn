--
--    author:  bernborgess
--    problem: Squares - lean-learn
--    created: 05.February.2024 01:31:57
--

def readLn : IO Nat := do return (←(←IO.getStdin).getLine).trim.toNat!

/--
Integer square root function. Implemented via Newton's method.
-/
def sqrt (n : Nat) : Nat :=
    if n ≤ 1 then n else
    iter n (n / 2)
    where
    /-- Auxiliary for `sqrt`. If `guess` is greater than the integer square root of `n`,
    returns the integer square root of `n`. -/
    iter (n guess : Nat) : Nat :=
        let next := (guess + n / guess) / 2
        if _h : next < guess then
        iter n next
        else
        guess
    termination_by iter guess => guess

def main : IO Unit := do
    let n ← readLn
    IO.println s!"The largest square has side length {sqrt n}."
