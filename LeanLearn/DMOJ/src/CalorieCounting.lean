--
--    author:  bernborgess
--    problem: CalorieCounting - lean-learn
--    created: 04.February.2024 21:57:04
--

def readLn : IO Nat := do
    let stdin ← IO.getStdin
    let i ← stdin.getLine
    match i.trim.toNat? with
    | none => return 0
    | some i => return i

def main : IO Unit := do
    let cals :=[
        [0,461,431,420,0].get! (← readLn),
        [0,100,57,70,0].get! (← readLn),
        [0,130,160,118,0].get! (← readLn),
        [0,167,266,75,0].get! (← readLn)
    ]
    let sm := cals.foldr Nat.add 0
    IO.println s!"Your total Calorie count is {sm}."
