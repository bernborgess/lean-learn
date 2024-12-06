-- Introducing Auxiliary Subgoals
variable (p q : Prop)

example (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left
  have hq : q := h.right
  show q ∧ p from And.intro hq hp

-- Lean also supports a structured way of reasoning backwards from a goal,
-- which models the "suffices to show" construction in ordinary mathematics.
-- The next example simply permutes the last two lines in the previous proof.

variable (p q : Prop)

example (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left
  suffices hq : q from And.intro hq hp
  show q from And.right h