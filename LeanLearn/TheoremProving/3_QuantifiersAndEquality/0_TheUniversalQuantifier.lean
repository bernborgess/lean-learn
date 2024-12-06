
-- The Universal Quantifier ∀

-- propositons as types in practice
example (α : Type) (p q : α → Prop) : (∀ x : α, p x ∧ q x) → ∀ y : α, p y :=
  λ h =>
  λ y =>
    have hpyqy := h y
    have hpy := hpyqy.left
    hpy
    

-- expresing transitivity
variable
  (α : Type)
  (r : α → α → Prop)
  (trans_r : ∀ x y z, r x y → r y z → r x z)
  (a b c : α)
  (hab : r a b)
  (hbc : r b c)

#check trans_r
#check trans_r a b c
#check trans_r a b c hab
#check trans_r a b c hab hbc

-- it's common to make these arguments implicit
variable
  (α : Type)
  (r : α → α → Prop)
  (trans_r : ∀ {x y z}, r x y → r y z → r x z)
  (a b c : α)
  (hab : r a b)
  (hbc : r b c)

#check trans_r
#check trans_r hab
#check trans_r hab hbc

-- Carrying elementary reasoning with equivalence relations
variable
  (α : Type)
  (r : α → α → Prop)
  (refl_r : ∀ x, r x x)
  (symm_r : ∀ {x y}, r x y → r y x)
  (trans_r : ∀ {x y z}, r x y → r y z → r x z)

example (a b c d : α) (hab : r a b) (hcb: r c b) (hcd : r c d) : r a d :=
  have hbc := symm_r hcb
  have hac := trans_r hab hbc
  show r a d from trans_r hac hcd

