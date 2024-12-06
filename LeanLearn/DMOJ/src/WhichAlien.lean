--
--    author:  bernborgess
--    problem: WhichAlien - lean-learn
--    created: 05.February.2024 00:58:05
--

def readLn : IO Nat := do return (←(←IO.getStdin).getLine).trim.toNat!

def main : IO Unit := do
    let a ← readLn
    let e ← readLn
    if a >= 3 && e <= 4 then IO.println "TroyMartian"
    if a <= 6 && e >= 2 then IO.println "VladSaturnian"
    if a <= 2 && e <= 3 then IO.println "GraemeMercurian"
