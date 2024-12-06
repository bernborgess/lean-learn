--
--    author:  bernborgess
--    problem: Flipper - lean-learn
--    created: 19.February.2024 00:30:31
--

open IO List

def getLine : IO String := do return (←(←getStdin).getLine).trim

inductive Cay
| e : Cay | tx : Cay | ty : Cay | r2 : Cay

def printCay
| Cay.e  => "1 2\n3 4" | Cay.tx => "3 4\n1 2"
| Cay.ty => "2 1\n4 3" | Cay.r2 => "4 3\n2 1"

instance : ToString Cay where
  toString := printCay

def app
| Cay.e,  'H' => Cay.tx
| Cay.e,  'V' => Cay.ty
| Cay.tx, 'H' => Cay.e
| Cay.tx, 'V' => Cay.r2
| Cay.ty, 'H' => Cay.r2
| Cay.ty, 'V' => Cay.e
| Cay.r2, 'H' => Cay.ty
| Cay.r2, 'V' => Cay.tx
| _,       _  => Cay.e

def main := getLine >>= println ∘ foldl app Cay.e ∘ String.toList
