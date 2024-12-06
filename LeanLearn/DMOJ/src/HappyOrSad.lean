--
--    author:  bernborgess
--    problem: HappyOrSad - lean-learn
--    created: 04.February.2024 23:04:47
--

def countFaces (s:List Char) : Int × Int := match s with
| ':' :: '-' :: x :: xs =>
    let dx := match x with
    | ')' => 1
    | '(' => (-1)
    | _   => 0
    let (fc,mt) := countFaces (x::xs)
    (fc+dx,mt+dx.natAbs)
| []        => (0,0)
| _ :: xs   => countFaces xs

def main : IO Unit := do
    let line ← (←IO.getStdin).getLine
    let (fc,mt) := countFaces line.toList
    let out := match compare fc 0 with
    | Ordering.lt => "sad"
    | Ordering.gt => "happy"
    | Ordering.eq => if mt > 0 then "unsure" else "none"
    IO.println out
