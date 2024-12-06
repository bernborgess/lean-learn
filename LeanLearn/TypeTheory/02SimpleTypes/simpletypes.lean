
-- Examples 2.3.1
-- (1) Typing a la Church
variable {α β γ : Type}
variable {x : α → α}
variable {y : (α → α) → β}
#check y x
variable {z : β}
variable {u : γ}
#check λ (z:β) (_u:γ) => z
#check (λ (z:β) (_u:γ) => z) (y x)

-- (2) Typing a la Curry
def M := (λ (z:β) (_u:γ) => z) (y x)

-- λzu.z : A → B
-- y z : A
-- M : B
-- z : A
-- λu.z : B ≡ (C → D)
-- u : C
-- z : D
-- y : E → F
-- x : E
-- y z : F
-- ==========
-- z : A ∧ z : D => A ≡ D
-- y x : A ∧ y x : F => A ≡ F
-- ∴
-- x : E, y : E → A, z : A, u : C
-- M : C → A


-- Example 2.3.2
def ex2 := λ (z : β) ↦ λ (_u : γ) ↦ z
variable {x : α → α}
variable {y : (α → α) → β}
#check ex2 (y x)
-- x : α → α, y : (α → α) → β ⊢ (λz:β.λu:γ.z)(y x) : γ → β

-- Remark 2.3.3
-- We do not have β-reduction yet for 'typed-terms', but
-- and educated guess it that
-- (λz:β.λu:γ.z)(y x) ->β λu:γ.y x
