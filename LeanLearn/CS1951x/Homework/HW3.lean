import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Nat.Basic
import Std.Data.Int.Lemmas
import Mathlib.Analysis.SpecialFunctions.Log.Basic


/- # FPV Homework 3: Forward Proofs

In this homework, you'll practice writing forward proofs.

Homework must be done in accordance with the course policies on collaboration
and academic integrity.

Replace the placeholders (e.g., `:= sorry`) with your solutions. When you are
finished, submit *only* this file to the appropriate Gradescope assignment.
Remember that the autograder does not determine your final grade. -/


/- ## Question 1 (4 points): Logic Puzzles

Consider the following tactical proof: -/

theorem about_Impl :
  ∀a b : Prop, ¬ a ∨ b → a → b :=
  by
    intros a b hor ha
    apply Or.elim hor
    { intro hna
      apply False.elim
      apply hna
      exact ha }
    { intro hb
      exact hb }

/- 1.1 (1 point). Prove the same theorem again, this time by providing a proof
term.

Hint: There is an easy way. -/

theorem about_Impl_term :
  ∀a b : Prop, ¬ a ∨ b → a → b :=
  λ a b hnab ha =>
    Or.elim hnab
    (λ hna : ¬ a => absurd ha hna)
    (λ hb : b => hb)


/- 1.2 (2 points). Prove the same theorem again, this time by providing a
structured proof, with `fix`, `assume`, and `show`. -/

theorem about_Impl_struct :
  ∀ a b : Prop, ¬ a ∨ b → a → b :=
  λ _a b hnab ha =>
  show b from Or.elim hnab (absurd ha ·) (·)

/-
1.3 (2 points). The following lemma will be helpful for part 4.
Prove it! For an extra challenge, prove it without using classical logic --
no `Classical.em` or `Classical.byContradiction`.
-/

theorem not_iff_not_self (P : Prop) : ¬ (P ↔ ¬ P) :=
  λ ⟨mp,mpr⟩ => match Classical.em P with
  | Or.inl hp  => mp hp hp
  | Or.inr hnp =>
    have hp := mpr hnp
    mp hp hp

example (Q : Prop) : ¬ (Q ↔ ¬ Q) :=
  not_iff_not_self Q


/- 1.4 (1 point). In a certain faraway village, there is only one barber for
the whole town. He shaves all those who do not shave themselves. Does the barber
shave himself?

Provide a structured proof showing that this premise implies `False`.
-/



section
  theorem false_of_barber
    (Person : Type)
    (shaves : Person → Person → Prop)
    (barber : Person)
    (h : ∀ x, shaves barber x ↔ ¬ shaves x x)
    : False :=
      have ⟨mp,mpr⟩ := h barber
      match Classical.em (shaves barber barber) with
      | Or.inl hb  => absurd hb (mp hb)
      | Or.inr hnb => absurd (mpr hnb) hnb
end



/-! ## Question 2 (6 points): Connectives and Quantifiers

2.1 (3 points). Supply a structured proof of the commutativity of `∨` under a
`∀` quantifier, using no other theorems than the introduction and elimination
rules for `∀`, `∨`, and `↔`. -/

-- theorem Or.symm {P Q : Prop} (h : P ∨ Q) : Q ∨ P := match h with
-- | Or.inl hp => Or.inr hp
-- | Or.inr hq => Or.inl hq


theorem Or_comm_under_All {α : Type} (p q : α → Prop) :
  (∀x, p x ∨ q x) ↔ (∀x, q x ∨ p x) :=
  Iff.intro
  (λ mp x => Or.symm (mp x))
  (λ mpr x => Or.symm (mpr x))

theorem Or_comm_under_All₂ {α : Type} (p q : α → Prop) :
  (∀x, p x ∨ q x) ↔ (∀x, q x ∨ p x) :=
  ⟨(Or.symm $ · ·),(Or.symm $ · ·)⟩



/-! ## Question 3 (2 points): Calc Mode
Use `calc` mode to prove that the difference of squares formula holds on the
integers. (In this particular problem, working on the integers is necessary, but
in practice not much different from working on ℕ.)

You might find some of the following lemmas useful!
-/
#check Int.mul_sub
#check sub_add_eq_sub_sub
#check sub_add
#check Int.add_sub_assoc
#check Int.sub_self
#check Int.mul_comm
#check Int.add_mul
#check Int.add_zero
#check Int.zero_add
#check Int.add_comm
#check sub_right_comm

theorem difference_of_squares (a b : ℤ) :
  (a + b) * (a - b) = a * a - b * b :=
  calc
    _ = (a + b) * (a - b)                 := by rw[]
    _ = a * (a - b) + b * (a - b)         := by rw[Int.add_mul]
    _ = a * a - a * b + b * (a - b)       := by rw[Int.mul_sub]
    _ = b * (a - b) + (a * a - a * b)     := by rw[Int.add_comm]
    _ = (b * a - b * b) + (a * a - a * b) := by rw[Int.mul_sub]
    _ = (a * b - b * b) + (a * a - a * b) := by rw[Int.mul_comm]
    _ = ((a * b - b * b) + a * a) - a * b := by rw[←Int.add_sub_assoc]
    _ = (a * a + (a * b - b * b)) - a * b := by rw[Int.add_comm]
    _ = a * a + a * b - b * b - a * b     := by rw[←Int.add_sub_assoc]
    _ = a * a + a * b - a * b - b * b     := by rw[sub_right_comm]
    _ = a * a - b * b                     := by rw[Int.add_sub_cancel]
