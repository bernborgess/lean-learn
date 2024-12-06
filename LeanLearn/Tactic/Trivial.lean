-- Extensible tactics by Macro expansion
syntax "custom_tactic" : tactic


macro_rules
| `(tactic| custom_tactic) => `(tactic| rfl)

macro_rules
| `(tactic| custom_tactic) => `(tactic| apply And.intro <;> custom_tactic)

example : 42 = 42 := by
  custom_tactic

example : 43 = 43 ∧ 42 = 42 := by
  custom_tactic

-- Implementing <;> : Tactic Combinators by Macro Expansion
syntax tactic " and_then " tactic : tactic

macro_rules
| `(tactic| $a:tactic and_then $b:tactic) =>
    `(tactic| $a:tactic; all_goals $b:tactic)

-- Test the tactic
theorem test_and_then : 1 = 1 ∧ 2 = 2 := by
  apply And.intro and_then rfl

#print test_and_then
