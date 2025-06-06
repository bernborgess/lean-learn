import Mathlib.Data.Nat.Basic
/- # FPV Lab 2: Backward Proofs

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/

set_option tactic.hygienic false

namespace LoVe

namespace BackwardProofs


/- ## Question 1: Connectives and Quantifiers

1.1. Carry out the following proofs using basic tactics.

Hint: Some strategies for carrying out such proofs are described at the end of
Section 3.3 in the Hitchhiker's Guide. -/

theorem I (a : Prop) : a → a := by
  intros
  assumption
  done

theorem K (a b : Prop) :
  a → b → b := by
  intros
  assumption
  done

theorem C (a b c : Prop) :
  (a → b → c) → b → a → c := by
  intro f hb ha
  apply f ha hb
  done

theorem proj_fst (a : Prop) :
  a → a → a := by
  intros
  assumption
  done

/- Please give a different answer than for `proj_fst`: -/

theorem proj_snd (a : Prop) :
  a → a → a := by
  intro _ha ha
  apply ha
  done

theorem some_nonsense (a b c : Prop) :
  (a → b → c) → a → (a → c) → b → c := by
  intro f ha g hb
  clear f hb
  apply g
  apply ha
  done

/- 1.2. Prove the contraposition rule using basic tactics. -/

theorem contrapositive (a b : Prop) :
  (a → b) → ¬ b → ¬ a := by
  intro f hnb ha
  have : b := f ha
  contradiction
  done

/- 1.3. Prove the distributivity of `∀` over `∧` using basic tactics.

Hint: This exercise is tricky, especially the right-to-left direction. Some
forward reasoning, like in the proof of `and_swap_braces` in the lecture, might
be necessary. -/

theorem forall_and {α : Type} (p q : α → Prop) :
  (∀x, p x ∧ q x) ↔ (∀x, p x) ∧ (∀x, q x) := by
  apply Iff.intro
  . intro h
    apply And.intro
    repeat
      intro x
      have ⟨hp,hq⟩ : p x ∧ q x := h x
      assumption
  . intro ⟨hp,hq⟩ x
    apply And.intro
    . apply hp x
    . apply hq x
  done


/- ## Question 2: Natural Numbers

2.1. Prove the following recursive equations on the first argument of the
`mul` operator defined in lecture 1. -/

def add : ℕ → ℕ → ℕ
  | m, Nat.zero   => m
  | m, Nat.succ n => Nat.succ (add m n)

def mul : ℕ → ℕ → ℕ
  | _, Nat.zero   => Nat.zero
  | m, Nat.succ n => add m (mul m n)


#check mul

theorem mul_zero (n : ℕ) :
  mul 0 n = 0 :=
  sorry

#check Nat.add_succ

theorem mul_succ (m n : ℕ) :
  mul (Nat.succ m) n = add (mul m n) n :=
  sorry

/- 2.2. Prove commutativity and associativity of multiplication using the
`induction` tactic. Choose the induction variable carefully. -/

theorem mul_comm (m n : ℕ) :
  mul m n = mul n m :=
  sorry

theorem mul_assoc (l m n : ℕ) :
  mul (mul l m) n = mul l (mul m n) :=
  sorry

/- 2.3. Prove the symmetric variant of `mul_add` using `rw`. To apply
commutativity at a specific position, instantiate the rule by passing some
arguments (e.g., `mul_comm _ l`). -/

theorem add_mul (l m n : ℕ) :
  mul (add l m) n = add (mul n l) (mul n m) :=
  sorry


/- ## Question 3 (**optional**): Intuitionistic Logic

As we discuss on this week's homework (see question 2.2), the rules we've been
working with so far describe *intuitionistic* logic. There are some things,
however, that "seem" true but can't be proved using just our intuitionistic
rules. (What are some of these things? We'll see momentarily!) To prove such
statements, we require *classical* logic.

Intuitionistic logic is extended to classical logic by assuming a classical
axiom. There are several possibilities for the choice of axiom. In this
question, we are concerned with the logical equivalence of three different
axioms: -/

def ExcludedMiddle : Prop :=
  ∀a : Prop, a ∨ ¬ a

def Peirce : Prop :=
  ∀a b : Prop, ((a → b) → a) → a

def DoubleNegation : Prop :=
  ∀a : Prop, (¬¬ a) → a

/- For the proofs below, avoid using theorems from Lean's `Classical` namespace.

3.1 (**optional**). Prove the following implication using tactics.

Hint: You will need `Or.elim` and `False.elim`. You can use
`rw [ExcludedMiddle]` to unfold the definition of `ExcludedMiddle`,
and similarly for `Peirce`. -/

theorem Peirce_of_EM :
  ExcludedMiddle → Peirce :=
  sorry

/- 3.2 (**optional**). Prove the following implication using tactics. -/

theorem DN_of_Peirce :
  Peirce → DoubleNegation :=
  sorry

/- We leave the remaining implication for the homework: -/

namespace SorryTheorems

theorem EM_of_DN :
  DoubleNegation → ExcludedMiddle :=
sorry

end SorryTheorems

end BackwardProofs

end LoVe
