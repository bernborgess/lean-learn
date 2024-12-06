
theorem prop_comp (a b c : Prop) (hab : a → b) (hbc : b → c) : a → c := hbc ∘ hab

theorem or_swap (a b : Prop) : a ∨ b → b ∨ a
| Or.inl ha => Or.inr ha
| Or.inr hb => Or.inl hb

theorem nat_exists_double_iden : ∃ n : Nat, n + n = n := ⟨0,rfl⟩

theorem nat_exists_double_iden₂ : ∃ n : Nat, n + n = n :=
  Exists.intro 0
    (show 0 + 0 = 0 from by rfl)

theorem modus_ponens (a b : Prop) : (a → b) → a → b := (· ·)


theorem modus_ponens₂ (a b : Prop) : (a → b) → a → b :=
  λ hab : a → b =>
  λ ha : a =>
  show b from hab ha
