
theorem fst : ∀ a b : Prop, a → (b → a) := by
    intro a
    intro b
    intro ha
    intro hb
    clear hb
    apply ha
    done

theorem fst₂ : ∀ a b : Prop, a → (b → a) := by
    intro a b ha _
    apply ha

theorem fst₃ : ∀ a b : Prop, a → (b → a) := by
    intros
    assumption

theorem And_swap₀ (a b : Prop) : a ∧ b → b ∧ a :=
    λ ⟨ha,hb⟩ => ⟨hb,ha⟩

theorem And_swap₁ (a b : Prop) : a ∧ b → b ∧ a := by
    intro ⟨ha,hb⟩
    exact ⟨hb,ha⟩

theorem And_swap₂ (a b : Prop) : a ∧ b → b ∧ a := by
    intro hab
    cases hab
    constructor
    repeat assumption
    done

theorem And_swap₃ (a b : Prop) : a ∧ b → b ∧ a := by
    intro hab
    apply And.intro
    apply And.right
    exact hab
    apply And.left
    exact hab
