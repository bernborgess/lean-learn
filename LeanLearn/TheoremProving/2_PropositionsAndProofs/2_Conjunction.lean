-- Conjunction
-- hask1
variable (p q : Prop)

example (hp : p) (hq : q) : p ∧ q := And.intro hp hq

#check fun (hp : p) (hq : q) => And.intro hp hq

variable (p q : Prop)

-- hask2
example (h : p ∧ q) : q ∧ p :=
  And.intro (And.right h) (And.left h)

variable (p q : Prop)
variable (hp : p) (hq : q)

#check (⟨hp, hq⟩ : p ∧ q)

variable (xs : List Nat)

#check List.length xs
#check xs.length

variable (p q : Prop)

example (h : p ∧ q) : q ∧ p :=
  ⟨h.right, h.left⟩

