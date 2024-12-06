-- Exercises
-- Prove the following identities, replacing the "sorry" placeholders with
-- actual proofs.
variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := 
  Iff.intro
    (λ h : p ∧ q => ⟨h.right,h.left⟩)
    (λ h : q ∧ p => ⟨h.right,h.left⟩)

example : p ∨ q ↔ q ∨ p := 
  Iff.intro
    (λ h : p ∨ q => 
      Or.elim h 
        (λ hp =>
          show q ∨ p from Or.inr hp)
        (λ hq =>
          show q ∨ p from Or.inl hq))
    (λ h : q ∨ p =>
      Or.elim h 
        (λ hq =>
          show p ∨ q from Or.inr hq)
        (λ hp =>
          show p ∨ q from Or.inl hp))
    
example : p ∨ q ↔ q ∨ p := Iff.intro
  (λ h => Or.elim h (λ hp => Or.inr hp) (λ hq => Or.inl hq))
  (λ h => Or.elim h (λ hq => Or.inr hq) (λ hp => Or.inl hp))

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := 
  Iff.intro
    (λ h : (p ∧ q) ∧ r =>
      have hpq : p ∧ q := h.left 
      have hp : p := hpq.left
      have hq : q := hpq.right
      have hr : r := h.right
      show p ∧ (q ∧ r) from ⟨hp,⟨hq,hr⟩⟩)
    (λ h =>
      have hp := h.left
      have hqr := h.right
      have hq := hqr.left
      have hr := hqr.right
      show (p ∧ q) ∧ r from ⟨⟨hp,hq⟩,hr⟩)

example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := Iff.intro
  (λ h => ⟨h.left.left,⟨h.left.right,h.right⟩⟩) 
  (λ h => ⟨⟨h.left,h.right.left⟩,h.right.right⟩)

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := 
  Iff.intro
    (λ h =>
      Or.elim h
        (λ hpq =>
          Or.elim hpq
            (λ hp =>
              show p ∨ (q ∨ r) from Or.inl hp)
            (λ hq =>
              show p ∨ (q ∨ r) from Or.inr (Or.inl hq))
        )
        (λ hr =>
          show p ∨ (q ∨ r) from Or.inr (Or.inr hr)))
    (λ h =>
      Or.elim h
        (λ hp =>
          show (p ∨ q) ∨ r from Or.inl (Or.inl hp))
        (λ hqr =>
          Or.elim hqr
            (λ hq =>
              show (p ∨ q) ∨ r from Or.inl (Or.inr hq))
            (λ hr => 
              show (p ∨ q) ∨ r from Or.inr hr)
        )
    )

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := 
  Iff.intro
    (λ h => 
      have hp := h.left
      have hqr := h.right
      Or.elim hqr
        (λ hq => Or.inl ⟨hp,hq⟩)
        (λ hr => Or.inr ⟨hp,hr⟩)
    )
    (λ h => 
      Or.elim h
        (λ hpq =>
          have hp := hpq.left
          have hq := hpq.right
          ⟨hp, Or.inl hq⟩ 
        )
        (λ hpr =>
          have hp := hpr.left
          have hr := hpr.right
          ⟨hp, Or.inr hr⟩ 
        )
    )

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := 
  Iff.intro
    (λ h => 
      Or.elim h
        (λ hp => ⟨Or.inl hp,Or.inl hp⟩)
        (λ hqr =>⟨Or.inr hqr.left,Or.inr hqr.right⟩)
    )
    (λ h =>
      have hpq := h.left
      have hpr := h.right
      Or.elim hpq
        (λ hp => Or.inl hp)
        (λ hq => 
          Or.elim hpr
            (λ hp => Or.inl hp)
            (λ hr => Or.inr ⟨hq,hr⟩)
        )
      )

-- other properties
def curry : (p ∧ q → r) → (p → q → r) := 
  λ h =>
  λ hp =>
  λ hq =>
    h ⟨hp,hq⟩


def uncurry : (p → (q → r)) → (p ∧ q → r) := 
  λ h => 
  λ hpq =>
  show r from h (hpq.left) (hpq.right)
 
example : (p → (q → r)) ↔ (p ∧ q → r) := 
  Iff.intro
    (uncurry p q r)
    (curry p q r)

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  Iff.intro
    (λ h => ⟨
      λ hp => h (Or.inl hp),
      λ hq => h (Or.inr hq)
    ⟩)
    (λ h =>
      have hpr := h.left
      have hqr := h.right
      λ hpq =>
        Or.elim hpq
          (λ hp => hpr hp)
          (λ hq => hqr hq)
    )


open Classical

theorem dne {p : Prop} (h : ¬¬p) : p :=
  Or.elim (em p)
  (λ hp : p => hp)
  (λ hnp : ¬p => absurd hnp h)

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

def andFalseIntroLeft : ¬p → ¬(p ∧ q) :=
  λ hnp : ¬p =>
  λ hnpq =>
     hnp (hnpq.left)

def andFalseIntroRight : ¬p → ¬(q ∧ p) :=
  λ hnp =>
  λ hnpq =>
    hnp (hnpq.right)

example : ¬p ∨ ¬q → ¬(p ∧ q) := 
  λ LHS : ¬p ∨ ¬q => 
  Or.elim LHS
    (andFalseIntroLeft p q)
    (andFalseIntroRight q p)

example : ¬(p ∧ ¬p) := 
  byContradiction
  λ hnn =>
    have h := dne hnn
    show False from h.right h.left 

example : p ∧ ¬q → ¬(p → q) := 
  λ hpnq =>
    have hp := hpnq.left
    have hnq := hpnq.right
    byContradiction
    λ hnnpq =>
      have hpq := dne hnnpq
      have hq := hpq hp
      show False from hnq hq

example : ¬p → (p → q) := 
  λ hnp =>
  λ hp => absurd hp hnp

example : (¬p ∨ q) → (p → q) := 
  λ hnpq =>
  Or.elim hnpq
    (λ hnp => λ hp => absurd hp hnp)
    (λ hq => λ _ => hq)

example : p ∨ False ↔ p := 
  Iff.intro
    (λ hpf =>
      Or.elim hpf
        (λ hp => hp)
        (λ hf => False.elim hf))
    (λ hp => Or.inl hp)

example : p ∧ False ↔ False := 
  Iff.intro
    (λ hpf =>
      have hf := hpf.right
      False.elim hf)
    (λ hf => False.elim hf)

example : (p → q) → (¬q → ¬p) := 
  λ hpq =>
  λ hnq =>
  byContradiction
  λ hnnp =>
    have hp := dne hnnp
    have hq := hpq hp
    show False from hnq hq

-- Prove the following identities, replacing the "sorry" placeholders with
-- actual proofs. These require classical reasoning.
open Classical

variable (p q r : Prop)

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
example : ¬(p ↔ ¬p) :=
  (λ contra: p ↔ ¬p =>
    have ida : p → ¬p := Iff.mp contra
    have volta : ¬p → p := Iff.mpr contra
    have hnp := λ hp => ida hp hp
    have hp := volta hnp
    False.elim (hnp hp)
  )






































