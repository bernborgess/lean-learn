-- Equality

-- A fundamental property of equality is that it is an equivalence relation:
#check Eq.refl
#check Eq.symm
#check Eq.trans

-- more readable
universe u

#check @Eq.refl.{u}
#check @Eq.symm.{u}
#check @Eq.trans.{u}

-- Specialize the previous example to the equality relation
variable
  (α : Type) (a b c d : α)
  (hab : a = b)
  (hcb : c = b)
  (hcd : c = d)

example : a = d :=
  have hbc := Eq.symm hcb
  have hac := Eq.trans hab hbc
  show a = d from Eq.trans hac hcd

-- projection notation
example : a = d := (hab.trans hcb.symm).trans hcd

-- Reflexivity is more powerful than in looks
-- terms in the `Calculus of Constructions` have a computational interpretation
variable (α β : Type)

example (f : α → β) (a : α) : (λ x => f x) a = f a := Eq.refl _
example (a : α) (b : β) : (a, b).1 = a := Eq.refl _

example : 2 + 3 = 5 := Eq.refl _

-- Equality is more than equivalence

example (α : Type) (a b : α) (p : α → Prop)
        (h1 : a = b) (h2 : p a) : p b :=
  Eq.subst h1 h2
        
example (α : Type) (a b : α) (p : α → Prop)
        (h1 : a = b) (h2 : p a) : p b :=
  h1 ▸ h2

-- Eq.subst defines three auxiliary rules

variable (α : Type)
variable (a b : α)
variable (f g : α → Nat)
variable (h₁ : a = b)
variable (h₂ : f = g)

example : f a = f b := congrArg f h₁
example : f a = g a := congrFun h₂ a
example : f a = g b := congr h₂ h₁
