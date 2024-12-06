-- Exercises
-- First exercise is to go back to Chapter Propositions and Proofs and
-- to Chapter Quantifiers and Equality and
-- redo it with tactic proofs, using rw and simp where appropriate.
variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := by
  apply Iff.intro
  . intro ⟨hp,hq⟩
    exact ⟨hq,hp⟩
  . intro ⟨hq,hp⟩
    exact ⟨hp,hq⟩

example : p ∨ q ↔ q ∨ p := by
  apply Iff.intro
  . intro h
    apply Or.elim h
    . intro hp
      exact Or.inr hp
    . intro hq
      exact Or.inl hq
  . intro h
    apply Or.elim h
    . intro hq
      exact Or.inr hq
    . intro hp
      exact Or.inl hp

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by
  apply Iff.intro
  . intro ⟨⟨hp,hq⟩,hr⟩; exact ⟨hp,⟨hq,hr⟩⟩
  . intro ⟨hp,⟨hq,hr⟩⟩; exact ⟨⟨hp,hq⟩,hr⟩

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := by
  apply Iff.intro
  . intro h
    apply Or.elim h
    . intro h
      apply Or.elim h
      . exact Or.inl
      . exact (Or.inr ∘ Or.inl)
    . exact (Or.inr ∘ Or.inr)
  . intro h
    apply Or.elim h
    . exact (Or.inl ∘ Or.inl)
    . intro h
      apply Or.elim h
      . exact (Or.inl ∘ Or.inr)
      . intro h
        exact Or.inr h


-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro ⟨hp,hqr⟩
    match hqr with
    | Or.inl hq => exact Or.inl ⟨hp,hq⟩
    | Or.inr hr => exact Or.inr ⟨hp,hr⟩
  . intro
    | Or.inl ⟨hp,hq⟩  => exact ⟨hp,Or.inl hq⟩
    | Or.inr ⟨hp,hr⟩  => exact ⟨hp,Or.inr hr⟩


example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by
  apply Iff.intro
  . intro
    | Or.inl hp => exact ⟨Or.inl hp,Or.inl hp⟩
    | Or.inr ⟨hq,hr⟩ => exact ⟨Or.inr hq,Or.inr hr⟩
  . intro ⟨hpq,hpr⟩
    match hpq with
    | Or.inl hp => exact Or.inl hp
    | Or.inr hq =>
      match hpr with
      | Or.inl hp => exact Or.inl hp
      | Or.inr hr => exact Or.inr ⟨hq,hr⟩

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := by
  apply Iff.intro
  . intro h ⟨hp,hq⟩
    exact h hp hq
  . intro h hp hq
    exact h ⟨hp,hq⟩


example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := by
  apply Iff.intro
  . intro h
    let fp := λ hp => h (Or.inl hp)
    let fq := λ hq => h (Or.inr hq)
    exact ⟨fp,fq⟩
  . intro ⟨hpr,hqr⟩
    intro
    | Or.inl hp => exact hpr hp
    | Or.inr hq => exact hqr hq


open Classical

theorem dne {p : Prop} (h : ¬¬p) : p := by
  apply Or.elim (em p)
  . exact id
  . intro hnp ; contradiction

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by
  apply Iff.intro
  . intro hnpq
    admit
  . admit

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  Iff.intro
    (λ hnpq: ¬(p ∨ q) =>
      ⟨byContradiction
       λ hnnp =>
        have hp := dne hnnp
        have hpq: p ∨ q := Or.inl hp
          show False from hnpq hpq
      ,
      byContradiction
       λ hnnq =>
        have hq := dne hnnq
        have hpq : p ∨ q := Or.inr hq
          show False from hnpq hpq
      ⟩
    )
    (λ hnpnq =>
      have hnp := hnpnq.left
      have hnq := hnpnq.right
      byContradiction
      (λ hnnpq  =>
        have hpq := dne hnnpq
        Or.elim hpq
          (λ hp: p => hnp hp)
          (λ hq: q => hnq hq)
      )
    )

example : ¬p ∨ ¬q → ¬(p ∧ q) := by
  intro
  | Or.inl hnp => intro ⟨hp,_⟩ ; contradiction
  | Or.inr hnq => intro ⟨_,hq⟩ ; contradiction

example : ¬(p ∧ ¬p) := by
  admit

example : ¬(p ∧ ¬p) :=
  byContradiction
  λ hnn =>
    have h := dne hnn
    show False from h.right h.left

example : p ∧ ¬q → ¬(p → q) := by
 admit

example : p ∧ ¬q → ¬(p → q) :=
  λ hpnq =>
    have hp := hpnq.left
    have hnq := hpnq.right
    byContradiction
    λ hnnpq =>
      have hpq := dne hnnpq
      have hq := hpq hp
      show False from hnq hq

example : ¬p → (p → q) := by
  intro hnp hp
  contradiction

example : (¬p ∨ q) → (p → q) := by
  intro
  | Or.inl hnp => intro ; contradiction
  | Or.inr hq => intro ; exact hq

example : p ∨ False ↔ p := by
  apply Iff.intro
  . intro
    | Or.inl hp => exact hp
    | Or.inr hf => contradiction
  . exact Or.inl

example : p ∧ False ↔ False := by
  apply Iff.intro
  . intro ⟨_,hf⟩ ; contradiction
  . intro hf ; contradiction


example : (p → q) → (¬q → ¬p) := by
  admit

example : (p → q) → (¬q → ¬p) :=
  λ hpq =>
  λ hnq =>
  byContradiction
  λ hnnp =>
    have hp := dne hnnp
    have hq := hpq hp
    show False from hnq hq



example : (p → q ∨ r) → ((p → q) ∨ (p → r)) := by
  intro h
  admit

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) :=
  λ h =>
  byCases
  (λ hp:p =>
    have hqor := h hp
    Or.elim hqor
    (λ hq => Or.inl (λ _ => hq))
    (λ hr => Or.inr (λ _ => hr))
  )
  (λ hnp =>
    Or.inl
    (λ hp:p =>
      show q from absurd hp hnp)
  )






example : ¬(p ∧ q) → ¬p ∨ ¬q := by
  admit

example : ¬(p ∧ q) → ¬p ∨ ¬q :=
  λ h =>
  byCases
  (λ hp:p =>
    byCases
    (λ hq:q => absurd ⟨hp,hq⟩ h)
    (λ hnq:¬q => Or.inr hnq)
  )
  (λ hnp:¬p => Or.inl hnp)
























example : ¬(p → q) → p ∧ ¬q :=
  λ h =>
  byCases
  (λ hp : p =>
    byCases
    (λ hq : q => absurd (λ _ => hq) h)
    (λ hnq : ¬q => ⟨hp,hnq⟩)
  )
  (λ hnp: ¬p =>
    have p2q : p → q := (λ hp: p => absurd hp hnp)
    absurd p2q h
  )

example : (p → q) → (¬p ∨ q) :=
 λ h =>
  byCases
  (λ hp:p =>
    have hq := h hp
    Or.inr hq)
  (λ hnp:¬p => Or.inl hnp)

example : (¬q → ¬p) → (p → q) :=
  λ h =>
  byCases
  (λ hq:q => (λ _ => hq))
  (λ hnq:¬q =>
    have hnp := h hnq
    show p → q from (λ hp:p => absurd hp hnp))

example : p ∨ ¬p := em p

example : (((p → q) → p) → p) :=
  λ h =>
  byCases
  (λ hp:p => hp)
  (λ hnp:¬p =>
    have k : p → q := (λ hp => absurd hp hnp)
    show p from h k)

-- Prove ¬(p ↔ ¬p) without using classical logic.
example : ¬(p ↔ ¬p) := by
  intro ⟨ida,volta⟩
  let hnp := λ hp => ida hp hp
  let hp := volta hnp
  contradiction
