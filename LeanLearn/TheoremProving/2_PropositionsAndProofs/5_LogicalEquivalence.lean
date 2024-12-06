-- The expression Iff.intro h1 h2 produces a proof of p ↔ q from h1 : p → q
-- and h2 : q → p. The expression Iff.mp h produces a proof of p → q from
-- h : p ↔ q. Similarly, Iff.mpr h produces a proof of q → p from h : p ↔ q.
-- Here is a proof of p ∧ q ↔ q ∧ p:
variable (p q : Prop)

theorem and_swap : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (fun h : p ∧ q =>
     show q ∧ p from And.intro (And.right h) (And.left h))
    (fun h : q ∧ p =>
     show p ∧ q from And.intro (And.right h) (And.left h))

#check and_swap p q    -- p ∧ q ↔ q ∧ p


variable (h : p ∧ q)
example : q ∧ p := Iff.mp (and_swap p q) h