import Lean

-- 1. Create an "urgent minus 💀" notation such that 5 * 8 💀 4 returns 20,
-- and 8 💀 6 💀 1 returns 3.

-- a) Using notation command.
/-
scoped notation:72 l:70 " 💀 " r:72 => (l - r)
#eval 5 * 8 💀 4
#eval 8 💀 6 💀 1
-/

-- b) Using infix command.
/-
set_option quotPrecheck false
infixr:72 " 💀 " => λ l r => (l - r)

#eval 5 * 8 💀 4
#eval 8 💀 6 💀 1
-/

-- c) Using syntax command.
/-
syntax:72 term:70 " 💀 " term:72 : term
macro_rules | `($l:term 💀 $r:term) => `($l -$r)

#eval 5 * 8 💀 4
#eval 8 💀 6 💀 1
-/

-- Hint: multiplication in Lean 4 is defined as infixl:70 " * " => HMul.hMul.

-- 2. Consider the following syntax categories: term, command, tactic;
-- and 3 syntax rules given below.
-- Make use of each of these newly defined syntaxes.

syntax "good morning" : term
syntax "hello" : command
syntax "yellow" : tactic

-- #eval good morning

-- hello

-- example : "blue" != "green" := by
--   yellow

-- Create a syntax rule that would accept the following commands:

-- red red red 4
-- blue 7
-- blue blue blue blue blue 18
-- (So, either all reds followed by a number; or all blues followed by a number; red blue blue 5 - shouldn't work.)

-- Use the following code template:
syntax (name := colors) (("blue"+) <|> ("red"+)) num : command


-- our "elaboration function" that infuses syntax with semantics
@[command_elab colors]
def elabColors : CommandElab := λ stx => Lean.logInfo "success!"

red red 4
