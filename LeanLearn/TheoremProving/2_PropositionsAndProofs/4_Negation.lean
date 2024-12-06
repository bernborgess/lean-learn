-- Negation and Falsity
-- Negation, ¬p, is actually defined to be p → False,
-- so we obtain ¬p by deriving a contradiction from p.
-- Similarly, the expression hnp hp produces a proof of False
-- from hp : p and hnp : ¬p. The next example uses both these
-- rules to produce a proof of (p → q) → ¬q → ¬p.
-- (The symbol ¬ is produced by typing \not or \neg.)
variable (p q : Prop)

example (hpq : p → q) (hnq : ¬q) : ¬p :=
  fun hp : p =>
  show False from hnq (hpq hp)

-- The connective False has a single elimination rule,
-- False.elim, which expresses the fact that anything follows
-- from a contradiction. This rule is sometimes called ex
-- falso (short for ex falso sequitur quodlibet),
-- or the principle of explosion.
variable (p q : Prop)

example (hp : p) (hnp : ¬p) : q := False.elim (hnp hp)

-- The arbitrary fact, q, that follows from falsity is an
-- implicit argument in False.elim and is inferred automatically.
-- This pattern, deriving an arbitrary fact from contradictory
-- hypotheses, is quite common, and is represented by `absurd`.

variable (p q : Prop)

example (hp : p) (hnp : ¬p) : q := absurd hp hnp

-- Here, for example, is a proof of ¬p → q → (q → p) → r:
variable (p q r : Prop)

example (hnp : ¬p) (hq : q) (hqp : q → p) : r :=
  absurd (hqp hq) hnp