namespace Playground2

-- The scoped modifier makes sure the syntax declarations remain in this `namespace`
-- because we will keep modifying this along the chapter
scoped syntax "⊥" : term -- ⊥ for false
scoped syntax "⊤" : term -- ⊤ for true
scoped syntax:40 term " OR " term : term
scoped syntax:50 term " AND " term : term
-- #check ⊥ OR (⊤ AND ⊥) -- elaboration function hasn't been implemented but parsing passes

end Playground2

declare_syntax_cat boolean_expr
syntax "⊥" : boolean_expr -- ⊥ for false
syntax "⊤" : boolean_expr -- ⊤ for true
syntax:40 boolean_expr " OR " boolean_expr : boolean_expr
syntax:50 boolean_expr " AND " boolean_expr : boolean_expr

syntax "[Bool|" boolean_expr "]" : term
-- #check [Bool| ⊥ AND ⊤] -- elaboration function hasn't been implemented but parsing passes


syntax binOne := "O"
syntax binZero := "Z"

syntax binDigit := binZero <|> binOne


-- the "+" denotes "one or many", in order to achieve "zero or many" use "*" instead
-- the "," denotes the separator between the `binDigit`s, if left out the default separator is a space
syntax binNumber := binDigit,+


syntax "bin(" binNumber ")" : term
-- #check bin(Z, O, Z, Z, O) -- elaboration function hasn't been implemented but parsing passes
-- #check bin() -- fails to parse because `binNumber` is "one or many": expected 'O' or 'Z'

syntax binNumber' := binDigit,* -- note the *
syntax "emptyBin(" binNumber' ")" : term
-- #check emptyBin() -- elaboration function hasn't been implemented but parsing passes


syntax "binCompact(" ("Z" <|> "O"),+ ")" : term
-- #check binCompact(Z, O, Z, Z, O) -- elaboration function hasn't been implemented but parsing passes


-- The (...)? syntax means that the part in parentheses is optional
syntax "binDoc(" (str ";")? binNumber ")" : term
-- #check binDoc(Z, O, Z, Z, O) -- elaboration function hasn't been implemented but parsing passes
-- #check binDoc("mycomment"; Z, O, Z, Z, O) -- elaboration function hasn't been implemented but parsing passes
