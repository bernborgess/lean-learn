import Mathlib.Data.Nat.Basic

/- # FPV Homework 2: Backward Proofs

In this homework, you'll practice writing *backward* (or *tactical*) proofs.

Homework must be done in accordance with the course policies on collaboration
and academic integrity.

Replace the placeholders (e.g., `:= sorry`) with your solutions. When you are
finished, submit *only* this file to the appropriate Gradescope assignment.
Remember that the autograder does not determine your final grade. -/


set_option autoImplicit false

namespace LoVe

namespace BackwardProofs


/- ## Question 1 (3 points): Connectives and Quantifiers

Complete the following proofs using basic tactics such as
`intro`, `apply`, and `exact`.

Hint: Some strategies for carrying out such proofs are described at the end of
Section 3.3 in the Hitchhiker's Guide.

Think about the similarity to the type inhabitation problems of HW1!
-/

theorem B (a b c : Prop) : (a → b) → (c → a) → c → b := by
  intro f g hc
  apply f
  apply g
  apply hc

theorem S (a b c : Prop) : (a → b → c) → (a → b) → a → c := by
  intro f g ha
  apply f
  apply ha
  apply g
  apply ha
  done

theorem more_nonsense (a b c : Prop) : (c → (a → b) → a) → c → b → a := by
  intro f hc hb
  apply f
  apply hc
  intros
  apply hb
  done

theorem or_can_swap (p q : Prop) : p ∨ q → q ∨ p := by
  intro hpq
  apply Or.elim hpq
  intro hp
  apply Or.inr hp
  intro hq
  apply Or.inl hq
  done


/- For an extra challenge: translate the `weak_peirce` type inhabitation
problem from HW1 into a theorem statement, and prove the theorem! -/



/- ## Question 2 (5 points): Logical Connectives

2.1 (1 point). Prove the following property about implication using basic
tactics.

Hints:

* Keep in mind that `¬ a` is defined as `a → False`. You can start by invoking
  `rw [Not]` if this helps you.

* You will need to apply the elimination rule for `∨` and the elimination rule
  for `False` at some point in the proof. -/

theorem about_Impl (a b : Prop) : ¬ a ∨ b → a → b := by
  intro hab ha
  apply Or.elim hab
  {
    intro hna
    apply absurd ha hna
  }
  {
    intro hb
    assumption
  }

/- 2.2 (2 points).

The logical rules we have seen so far describe *intuitionistic* logic.
There are some statements that we can't prove using only these rules,
despite them perhaps "seeming" true.
(Food for thought: how could I argue that we *can't* prove certain propositions?)

Intuitionistic logic is extended to *classical* logic by assuming a classical
axiom, that allows us to prove these missing statements.
There are several possibilities for the choice of axiom. In this
question, we are concerned with the logical equivalence of three different
axioms: -/

def ExcludedMiddle : Prop :=
  ∀a : Prop, a ∨ ¬ a

def Peirce : Prop :=
  ∀a b : Prop, ((a → b) → a) → a

def DoubleNegation : Prop :=
  ∀a : Prop, (¬¬ a) → a

/-! For the proofs below, avoid using theorems from Lean's `Classical` namespace.


We will prove the equivalence of these axioms: each one implies the others.

Hints:

* One way to find the definitions of `DoubleNegation` and `ExcludedMiddle`
  quickly is to

  1. hold down the Control (on Linux and Windows) or Command (on macOS) key;
  2. move the cursor to the identifier `DoubleNegation` or `ExcludedMiddle`;
  3. click the identifier.

* You can use `rw [DoubleNegation]` to unfold the definition of
  `DoubleNegation`, and similarly for the other definitions.

* You will need to apply the double negation hypothesis for `a ∨ ¬ a`. You will
  also need the left and right introduction rules for `∨` at some point.
-/

#check DoubleNegation
#check ExcludedMiddle



theorem not_em_implies_not_p {p : Prop} (h : ¬(p ∨ ¬p)) : ¬p :=
  λ hp =>
  have em : p ∨ ¬p := Or.inl hp
  show False from h em

theorem not_em_implies_em {p : Prop} (h : ¬(p ∨ ¬p)) : (p ∨ ¬p) :=
  have hnp : ¬p := not_em_implies_not_p h
  show (p ∨ ¬p) from Or.inr hnp

theorem not_not_em_holds {p : Prop} : ¬¬(p ∨ ¬p) :=
  λ hnem : ¬(p ∨ ¬p) =>
  show False from absurd (not_em_implies_em hnem) hnem

theorem EM_of_DN : DoubleNegation → ExcludedMiddle := by
  intro hdne a
  have not_not_em : ¬¬(a ∨ ¬a) := not_not_em_holds
  apply hdne
  apply not_not_em
  done


/-

In this week's lab, you'll have the option to prove a few more implications.
We state them `sorry`ed here, for reference and use;
you don't need to prove these for this homework.

-/

theorem Peirce_of_EM : ExcludedMiddle → Peirce := by
  intro hem a b f
  cases hem a with
  | inl ha  => assumption
  | inr hna =>
    have hab : a → b := λ ha => absurd ha hna
    apply f hab

theorem DN_of_Peirce : Peirce → DoubleNegation := by
  intro hpei a hnna     -- a
  apply hpei            -- (a → ?b) → a
  intro haf             -- a
  apply False.elim      -- False
  apply hnna haf
  done


theorem DN_of_Peirce₂ : Peirce → DoubleNegation := by
  intro hpei a hnna     -- a
  apply hpei            -- (a → ?b) → a
  intro haf             -- a
  contradiction         -- resolves ?b to False, haf : a → False ≡ ¬a
                        -- contradicts ¬¬a with ¬a
  done


/- 2.3 (2 points). We have three of the six possible implications
between `ExcludedMiddle`, `Peirce`, and `DoubleNegation`. State and prove the
three missing implications, exploiting the three theorems we already have. -/


-- enter your solution here
theorem Peirce_of_DN : DoubleNegation → Peirce      := Peirce_of_EM ∘ EM_of_DN

theorem EM_of_Peirce : Peirce → ExcludedMiddle      := EM_of_DN ∘ DN_of_Peirce

theorem DN_of_EM : ExcludedMiddle → DoubleNegation  := DN_of_Peirce ∘ Peirce_of_EM



/-! ## Question 3 (3 points): Equality

You may hear it said that equality is the smallest *reflexive*, *symmetric*,
*transitive* relation. The following exercise shows that in the presence of
reflexivity, the rules for symmetry and transitivity are equivalent to a single
rule, "symmtrans". -/

axiom symmtrans {A : Type} {a b c : A} : a = b → c = b → a = c

-- You can now use `symmtrans` as a rule.

example (A : Type) (a b c : A) (h1 : a = b) (h2 : c = b) : a = c := by
  apply symmtrans
  apply h1
  apply h2

example (A : Type) (a b c : A) (h1 : a = b) (h2 : c = b) : a = c := symmtrans h1 h2

section

variable {A : Type}
variable {a b c : A}

/-! Replace the `sorry`s below with proofs, using `symmtrans` and `rfl`, without
using `Eq.symm`, `Eq.trans`, or `Eq.subst`. You should not use any tactics
besides `apply`, `exact`, and `rfl`. -/

theorem my_symm (h : b = a) : a = b := by
  apply symmtrans
  rfl
  apply h
  done

theorem my_trans (h1 : a = b) (h2 : b = c) : a = c := by
  apply symmtrans h1
  apply symmtrans
  rfl
  apply h2
  done
end


/-! ## Question 4 (3 points): Pythagorean Triples

A Pythagorean triple is a "triple" of three natural numbers `a`,
`b`, and `c` such that `a² + b² = c²`, i.e., they are integer sides of a right
triangle. -/

def IsPythagoreanTriple (a b c : ℕ) : Prop :=
  a^2 + b^2 = c^2

/-! By assuming Fermat's Last Theorem
(https://en.wikipedia.org/wiki/Fermat%27s_Last_Theorem), we can show that if
`a`, `b`, and `c` form a Pythagorean triple, then `a`, `b`, and `c` can't all be
perfect squares. Use the definitions below to prove this. -/

axiom fermats_last_theorem (x y n : ℕ) :
  (n ≥ 3) → ¬∃ (z : ℕ), x^n + y^n = z^n

def IsSquare (n : ℕ) : Prop := ∃ (u : ℕ), n = u^2

-- **Note**: You may use the following lemma in your proof.
lemma square_square (a b c : ℕ) : (a^2)^2 + (b^2)^2 = (c^2)^2 → a^4 + b^4 = c^4 := by
  intro h
  rw [←Nat.pow_mul, ←Nat.pow_mul, ←Nat.pow_mul] at h
  exact h

/-! Hints:
* `And.elim` behaves a bit weirdly. If you want to extract proofs of `P` and `Q`
  from a proof of a conjunction `h : P ∧ Q`, use `h.elim` rather than
  `And.elim h`.
* If you have a hypothesis `h : a = b` and want to replace `b` with `a` in your
  goal (instead of `a` with `b`), use `rw [←h]` (note the `←`).
* You can use the `decide` tactic to prove that `4 ≥ 3`.

Note: You may not use `simp` in your solution. (If you need to expand a
definition, you can use `rw`.) -/

lemma four_gt_3 : 4 >= 3 := by decide

theorem pythagorean_triple_not_all_squares (a b c : ℕ) :
  IsPythagoreanTriple a b c → ¬(IsSquare a ∧ IsSquare b ∧ IsSquare c) := by
  intro ht ⟨⟨ua,ha⟩,⟨ub,hb⟩,⟨uc,hc⟩⟩
  have quad := square_square ua ub uc
  have subt := fermats_last_theorem ua ub 4 four_gt_3
  apply subt
  apply Exists.intro
  apply quad
  rw [←ha,←hb,←hc]
  apply ht
  done


end BackwardProofs

end LoVe
