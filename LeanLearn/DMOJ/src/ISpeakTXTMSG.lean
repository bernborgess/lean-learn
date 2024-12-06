--
--    author:  bernborgess
--    problem: ISpeakTXTMSG - lean-learn
--    created: 07.March.2024 12:31:46
--

open IO

def getLine : IO String := do return (←(←getStdin).getLine).trim

def shorts := [
  ("CU","see you"),
  (":-)","I'm happy"),
  (":-(","I'm unhappy"),
  (";-)","wink"),
  (":-P","stick out my tongue"),
  ("(~.~)","sleepy"),
  ("TA","totally awesome"),
  ("CCC","Canadian Computing Competition"),
  ("CUZ","because"),
  ("TY","thank-you"),
  ("YW","you're welcome"),
  ("TTYL","talk to you later")
]

partial def main : IO Unit := do
  let line ← getLine
  println <| shorts.lookup line |>.getD line
  if line ≠ "TTYL" then main
