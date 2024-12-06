
/- # Principios da logica classica -/
variable {A B : Prop}

/- ## Identidade -/
example : A → A :=
  λ a ↦ a

/- ## Terceiro Excluido -/
example : A ∨ ¬ A := Classical.em A

/- ## Lei da nao contradicao -/
example : ¬(A ∧ ¬A) :=
  λ hana ↦
    have ha : A := And.left hana
    have hna : ¬A := And.right hana
    have hf : False := hna ha
    show False from hf

/- ## Modus Ponens -/
example : (A → B) → A → B :=
  λ hab : A → B ↦
  λ ha : A ↦
    show B from hab ha

/- ## Modus Tollens -/
theorem modus_tollens : (A → B) → ¬B → ¬A :=
  λ hab : A → B ↦
  λ hnb : ¬B ↦
    Or.elim (Classical.em A)
    (λ ha : A ↦
      have hb : B := hab ha
      show ¬A from absurd hb hnb
    )
    (λ hna : ¬A ↦ hna)

/- ## Principio da Explosao -/
example : A → ¬A → B :=
  λ ha : A ↦
  λ hna : ¬A ↦
    have hf : False := hna ha
    show B from False.elim hf

/- # Regras de Inferencia Primitivas -/

/- ## Introducao da Conjuncao -/
#check And.intro

/- ## Eliminacao da Conjuncao -/
#check And.left
#check And.right

/- ## Introducao da Disjuncao -/
#check Or.inl
#check Or.inr

/- ## Eliminacao da Disjuncao -/
#check Or.elim

/- ## Introducao da Implicacao -/
#check Function.const

example : B → A → B :=
  λ b ↦ λ _ ↦ b

/- ## Eliminacao da Implicacao -/
example : A → (A → B) → B :=
  λ a ↦ λ hab ↦ hab a

-- #check <| $

/- ## Terceiro Excluido -/
example : A ∨ ¬A := Classical.em A

/- ## Principio da Explosao -/
example : A → ¬A → B :=
  λ a ↦ λ na ↦ absurd a na

-- Prove ¬(p ↔ ¬p) without using classical logic.
example : ¬(p ↔ ¬p) :=
  (λ contra: p ↔ ¬p =>
    have ⟨ida,volta⟩ := contra
    have hnp : ¬p := λ hp => ida hp hp
    have hp : p := volta hnp
    False.elim (hnp hp)
  )

theorem MTP : (P ∨ Q) → ¬P → Q :=
  λ hpq => λ hnp => Or.elim hpq
    (λ h : P => absurd h hnp)
    (λ h : Q => h)

-- Exercicio
theorem exercicio (h : p → q) : ¬q → ¬p := by
  intro (hnq : ¬q)
  intro (hp : p)
  have hq : q := h hp
  apply show False from hnq hq
  done

example (h1 : P → Q) (h2 : ¬P → (Q ∨ R)) (h3: ¬Q) : R :=
  have hnp : ¬P := modus_tollens h1 h3
  have hqr : Q ∨ R := h2 hnp
  have hr : R := MTP hqr h3
  show R from hr

def semantic (α : Prop) [Decidable α] : Bool :=
  if _ : α then true else false

-- def isOk (n : Nat) :=
--   if h : n > 0 then true else false

example : p → (p → q) → q :=
  λ hp => λ hpq => hpq hp

