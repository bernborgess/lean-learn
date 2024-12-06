

example (h : p → q) (i : q → ¬r) : p ∨ r := by
  have k : ¬q → ¬p := λ hq hp ↦ hq (h hp)
  by_cases hp : p
  . exact Or.inl hp
  .
    sorry
  done
