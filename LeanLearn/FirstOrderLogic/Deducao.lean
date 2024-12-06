import Paperproof

theorem t1 (h1 : Γ → B) (h2 : Δ → B → A) : Γ → Δ → A := by
  intro hg hd
  have hb : B := h1 hg
  exact show A from h2 hd hb
  done


example (h : A ∧ B) : A := And.left h

example (h : A) : A ∨ B := Or.inl h

example
  (h1 : Γ → A → B → (A → B))
  (h2 : Γ → A → B)
  : Γ → (A → B) :=
  Classical.byContradiction
  (λ h => sorry)
