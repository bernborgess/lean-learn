--
--    author:  bernborgess
--    problem: VoronoiVillages - lean-learn
--    created: 22.February.2024 23:56:41
--

open IO

def replicateM : Nat → IO α → IO (List α)
| 0, _     => return []
| k + 1, f => return (←f) :: (←replicateM k f)

def getLine : IO String := do return (←(←getStdin).getLine).trim
def readLn : IO Int := do return (←getLine).toInt!

def sort [LT α] [DecidableRel ((·<·) : α → α → Prop)  ] : List α → List α :=
  Array.toList ∘ flip Array.qsort (·<·) ∘ Array.mk

def inf : Int := 2000000000

def find : List Int → Int
| (x::y::z::xs) => min (z-x) $ find (y::z::xs)
| _             => inf

def Float.toStringPrecision (n := 6) (f : Float) : String :=
  let rm := 6 - n
  let nl := f.toString.toList.reverse.drop rm
  String.mk nl.reverse

def main : IO Unit := do
  let N ← readLn
  let V ← sort <$> replicateM N.toNat readLn
  let d := (·/2.0) ∘ Float.ofInt $ find V
  println $ d.toStringPrecision 1
