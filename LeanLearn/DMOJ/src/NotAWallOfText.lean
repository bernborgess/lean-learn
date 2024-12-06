--
--    author:  bernborgess
--    problem: NotAWallOfText - lean-learn
--    created: 12.February.2024 13:28:13
--

open IO List

def getLine : IO String := do return (←(←IO.getStdin).getLine).trim

def main : IO Unit := getLine >>= println ∘ length ∘ flip String.split Char.isWhitespace
