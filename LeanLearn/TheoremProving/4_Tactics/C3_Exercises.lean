-- Exercises
-- First exercise is to go back to Chapter Propositions and Proofs and
-- to Chapter Quantifiers and Equality and
-- redo it with tactic proofs, using rw and simp where appropriate.
variable (α : Type) (p q : α → Prop)


example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := by
  apply Iff.intro
  . intro ha
    exact ⟨λ x => (ha x).left, λ x => (ha x).right⟩
  . intro ⟨hap, haq⟩ x
    exact ⟨hap x, haq x⟩

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := by
  intro hpq hp x
  exact (hpq x) (hp x)

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := by
  intro
  | Or.inl hp =>
      intro x ; exact (Or.inl (hp x))
  | Or.inr hq =>
      intro x ; exact (Or.inr (hq x))


variable (r : Prop)

example : α → ((∀ _ : α, r) ↔ r) := by
  intro x
  apply Iff.intro
  . intro h ; exact h x
  . intro r _ ; exact r


open Classical

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := by
  apply Iff.intro
  . admit
  . intro
    | Or.inl ha => intro x ; exact Or.inl (ha x)
    | Or.inr hr => intro ; exact Or.inr hr

def all_or_split : (∀ (x : α), p x ∨ r) → (∀ (x : α), p x) ∨ r :=
  λ h =>
    byCases
    (λ hr : r => Or.inr hr)
    (λ hnr =>
      have k : (∀ (x : α), p x) :=
        λ x => Or.elim (h x)
          id (λ hr => absurd hr hnr)
      Or.inl k)

def or_all_split : (∀ (x : α), p x) ∨ r → ∀ (x : α), p x ∨ r :=
  λ h => λ x =>
    Or.elim h
    (λ ha => Or.inl (ha x))
    (λ hr => Or.inr hr)

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
  Iff.intro
  (all_or_split α p r)
  (or_all_split α p r)


example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := by
  apply Iff.intro
  . intro h hr x ; exact (h x) hr
  . intro h x hr ; exact (h hr) x


-- 3. Consider the `barber paradox` that is, the claim that in a certain town
-- there is a (male) barber that shaves all and only the men who do not shave
-- themselves. Prove that this is a contradiction:

variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False := by
  admit

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False :=
  byCases
  (λ s : shaves barber barber =>
    absurd s ((h barber).mp s))
  (λ ns =>
    absurd ((h barber).mpr ns) ns)
