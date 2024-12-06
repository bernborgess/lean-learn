-- Working with Propositions as Types
-- In the propositions-as-types paradigm, theorems involving only
-- → can be proved using lambda abstraction and application.
-- In Lean, the theorem command introduces a new theorem:
variable {p : Prop}
variable {q : Prop}

theorem t1 : p → q → p :=
  λ hp : p =>
  λ _hq : q => -- hp
  -- explicitly
  show p from hp

#print t1

-- As with ordinary definitions, we can move the
-- lambda-abstracted variables to the left of the colon:
theorem t1' (hp : p) (_hq : q) : p := hp

#print t1'

-- Now we can apply the theorem t1 just as a function
-- application.
axiom hp : p

theorem t2 : q → p := t1 hp

-- Here, the axiom declaration postulates the existence
-- of an element of the given type and may compromise
-- logical consistency. For example, we can use it to
-- postulate the empty type False has an element.
axiom unsound : False
-- Everything follows from false
-- ex falso quodlibet
theorem ex : 1 = 0 :=
  False.elim unsound



-- When we generalize t1 in such a way, we can then apply it to
-- different pairs of propositions, to obtain different instances
-- of the general theorem.
theorem t1'' (p q : Prop) (hp : p) (_hq : q) : p := hp

variable (p q r s : Prop)

#check t1'' p q                -- p → q → p
#check t1'' r s                -- r → s → r
#check t1'' (r → s) (s → r)    -- (r → s) → (s → r) → r → s

variable (h : r → s)
#check t1'' (r → s) (s → r) h  -- (s → r) → r → s

variable (p q r s : Prop)

theorem t2' (h₁ : q → r) (h₂ : p → q) : p → r :=
  fun h₃ : p =>
  show r from h₁ (h₂ h₃)
