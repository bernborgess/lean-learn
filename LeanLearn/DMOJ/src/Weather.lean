--
--    author:  bernborgess
--    problem: Weather - lean-learn
--    created: 20.February.2024 21:50:49
--

open IO

def getLine : IO String := do return (←(←getStdin).getLine).trim
def readLn : IO Int := do return (←getLine).toInt!
def main := readLn >>= println ∘ (· * 9.0 / 5.0 + 32.0) ∘ Float.ofInt
