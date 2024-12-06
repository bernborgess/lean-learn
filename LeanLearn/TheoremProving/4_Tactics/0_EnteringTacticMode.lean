
example (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p :=
  ⟨hp, hq, hp⟩

-- We can use a `by <tactics>` block
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  exact hp
  apply And.intro
  exact hq
  exact hp

theorem test2 (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  . exact hp
  . apply And.intro
    . exact hq
    . exact hp

#print test
