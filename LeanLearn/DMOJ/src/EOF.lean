
open IO

def getLine : IO String := do return (←(←getStdin).getLine).trim


/-- Reads lines from stdin until EOF and returns the count of lines read. -/
partial def countLinesUntilEOF : IO Nat := do
  let rec loop (count : Nat) := do
    (do
      let _ ← getLine
      loop (count + 1)
    ) <|> pure count  -- When EOF is encountered, return the count
  loop 0

def main : IO Unit := do
  let count ← countLinesUntilEOF
  println! "Total lines read: {count}"
