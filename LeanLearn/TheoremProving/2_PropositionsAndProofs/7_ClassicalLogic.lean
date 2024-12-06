-- Classical Logic
-- The introduction and elimination rules we have seen so far are all
-- `constructive`, which is to say, they reflect a computational understanding
-- of the logical connectives based on the propositions-as-types correspondence.
-- Ordinary classical logic adds to this the law of the `excluded middle`,
-- p ∨ ¬p. To use this principle, you have to open the classical namespace.
open Classical

variable (p : Prop)
#check em p

-- Intuitively, the constructive "Or" is very strong: asserting p ∨ q amounts
-- to knowing which is the case. If RH represents the Riemann hypothesis,
-- a classical mathematician is willing to assert RH ∨ ¬RH, even though we
-- cannot yet assert either disjunct.

-- One consequence of the law of the excluded middle is the principle of
-- `double-negation elimination`:
open Classical

theorem dne {p : Prop} (h : ¬¬p) : p :=
  Or.elim (em p)
    (fun hp : p => hp)
    (fun hnp : ¬p => absurd hnp h)

-- Double-negation elimination allows one to prove any proposition, p,
-- by assuming ¬p and deriving false, because that amounts to proving ¬¬p.
-- In other words, double-negation elimination allows one to carry out a
-- proof by contradiction, something which is not generally possible in
-- constructive logic.
-- As an exercise, you might try proving the converse, that is, showing that
-- `em` can be proved from dne. ¬easy

-- The classical axioms also give you access to additional patterns of proof
-- that can be justified by appeal to em. For example, one can carry out a
-- `proof by cases`:
example (h : ¬¬p) : p :=
  byCases
    (λ h1 : p => h1)
    (λ h1 : ¬p => absurd h1 h)

-- Or you can carry out a `proof by contradiction`:
example (h : ¬¬p) : p :=
  byContradiction
    (λ h1 : ¬p =>
      show False from h h1)

-- If you are not used to thinking constructively, it may take some time for you
-- to get a sense of where classical reasoning is used. It is needed in the
-- following example because, from a constructive standpoint, knowing that
-- p and q are not both true does not necessarily tell you which one is false:
example (h : ¬(p ∧ q)) : ¬p ∨ ¬q :=
  Or.elim (em p)
    (λ hp : p =>
      Or.inr
        (show ¬q from
          λ hq : q =>
          h ⟨hp, hq⟩))
    (λ hp : ¬p =>
      Or.inl hp)


-- an example that requires classical reasoning
example (p q : Prop) : ¬(p ∧ ¬q) → (p → q) :=
  λ h : ¬(p ∧ ¬q) =>
  λ hp : p =>
  show q from
    Or.elim (em q)
      (λ hq : q => hq)
      (λ hnq : ¬q => absurd ⟨hp,hnq⟩ h)

  