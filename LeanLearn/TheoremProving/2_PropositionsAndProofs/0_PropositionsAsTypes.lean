def Implies (p q : Prop) : Prop := p → q

#check And     -- Prop → Prop → Prop
#check Or      -- Prop → Prop → Prop
#check Not     -- Prop → Prop
#check Implies -- Prop → Prop → Prop

variable (p q r : Prop)
#check And p q                      -- Prop
#check Or (And p q) r               -- Prop
#check Implies (And p q) (And q p)  -- Prop

structure Proof (p : Prop) : Type where
  proof : p

#check Proof   -- Proof : Prop → Type

axiom and_comm (p q : Prop) : Proof (Implies (And p q) (And q p))

variable (p q : Prop)
#check and_comm p q     -- Proof (Implies (And p q) (And q p))

axiom modus_ponens : (p q : Prop) → Proof (Implies p q) → Proof p → Proof q

axiom implies_intro : (p q : Prop) → (Proof p → Proof q) → Proof (Implies p q)


-- In any case, all that really matters is the bottom line.
-- To formally express a mathematical assertion in the language of
-- dependent type theory, we need to exhibit a term p : Prop.
-- To prove that assertion, we need to exhibit a term t : p.
-- Lean's task, as a proof assistant, is to help us to construct such
-- a term, t, and to verify that it is well-formed and has the correct
-- type.
