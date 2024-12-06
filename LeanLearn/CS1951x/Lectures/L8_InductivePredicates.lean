import Mathlib.Data.Nat.Basic

/-
### Even Numbers

Mathematicians often define sets as the smallest that meets some criteria.
For example:

  The set `E` of even natural numbers is defined as the smalllest set closed
  under the following rules: (1) `0 ∈ E` and (2) for every `k ∈ ℕ`, if
  `k ∈ E`, then `k + 2 ∈ E`.

In Lean, we can define the corresponding "is even predicate as follows: -/

inductive Even : ℕ → Prop where
  | zero : Even 0
  | add_two : ∀ k : ℕ, Even k → Even (k + 2)

theorem Even_2 : Even 2 :=
  Even.add_two 0 Even.zero

theorem Even_4 : Even 4 :=
  Even.add_two 2 Even_2

-- How to prove that ¬ Even 1 ???

-- Why cannot we simply define `Even` recursively? Indeed, why not?

def evenRec : ℕ → Bool
| 0     => true
| 1     => false
| k + 2 => evenRec k

-- The recursive version requires us to specify a false case (1), and it
-- requires us to worry about termination. Because it is computational,
-- it works well with `rfl`, `simp`, `#reduce` and `#eval`.

-- The inductive version is considered more abstract and elegant. Each rule
-- is stated independently of the others.

-- #eval Even 0 -- failed to synthesize Decidable (Even 0)

instance : Decidable (Even 0) :=
  Decidable.isTrue Even.zero

#eval Even 0
-- Proving in general that even is decidable

def evenNonrec (k : ℕ) : Prop := k % 2 == 0

example : ¬ Even 1 := by
  intro he
  cases he -- does not match any constructors...


/-
### Tennis Games

Transition systems consist of transitions rules, which together specify a
binary predicate connecting a "before" and an "after" state. As a simple
specimen of a transition system, we consider the possible transitions, in
a game of tennis, starting form 0-0. -/

inductive Score : Type where
| vs        : ℕ → ℕ → Score
| advServ   : Score
| advRecv   : Score
| gameServ  : Score
| gameRecv  : Score

infixr:50 " – " => Score.vs

inductive Step : Score → Score → Prop where
| serv_0_15     : ∀ n, Step (0–n) (15–n)
| serv_15_30    : ∀ n, Step (15–n) (30–n)
| serv_30_40    : ∀ n, Step (30–n) (40–n)
| serv_40_game  : ∀ n, n < 40 → Step (40–n) Score.gameServ
| serv_40_adv   : Step (40–40) Score.advServ
| serv_adv_40   : Step Score.advServ (40–40)
| serv_adv_game : Step Score.advServ Score.gameServ
| recv_0_15     : ∀ n, Step (n–0) (n–15)
| recv_15_30    : ∀ n, Step (n–15) (n–30)
| recv_30_40    : ∀ n, Step (n–30) (n–40)
| recv_40_game  : ∀ n, n < 40 → Step (n–40) Score.gameRecv
| recv_40_adv   : Step (40–40) Score.advRecv
| recv_adv_40   : Step Score.advRecv (40–40)
| recv_adv_game : Step Score.advRecv Score.gameRecv

infixr:45 " ↝ " => Step

-- Can the score ever return to 0–0 ?
theorem no_Step_to_0_0 (s : Score) : ¬ s ↝ 0–0 := by
  intro hs
  cases hs
  done

example : ¬ Even 1 := by
  intro he
  cases he

/- ### Reflexive Transitive Closure

Our last introductory example is the reflexive transitive closure of a
relation `R`, modeled as a binary predicate `Star R`.  -/

inductive Star {α : Type} (R : α → α → Prop) : α → α → Prop
where
  | base (a b : α)    : R a b → Star R a b
  | refl (a : α)      : Star R a a
  | trans (a b c : α) : Star R a b → Star R b c → Star R a c

/-! The first rule embeds `R` into `Star R`. The second rule achives the
reflexive closure. The third rule achives the transitive closure.

The definition is truly elegant. If you doubt this, try implementing `Star`
as a recursive function: -/

def starRec {α : Type} (R : α → α → Bool) :
  α → α → Bool :=
  sorry




example : Star Step (0–0) Score.gameServ := by
  repeat -- apply these 3 steps until they fail
    apply Star.trans
    { apply Star.base
      constructor }

  apply Star.base
  constructor
  exact show 0 < 40 from Nat.succ_pos 39

  done



/- ### A Nonexample

Not all inductive definitions are legal. -/

-- fails
/-
inductive Illegal : Prop where
| intro : ¬ Illegal → Illegal

! (kernel) arg #1 of 'Illegal.intro' has a non positive occurrence
! of the datatypes being declared

This is an unsound proposition. Elimination and intro are the same rule.
-/

/- ### Logical Symbols

The truth values `False` and `True`
-/

/-! ## Elimination

Given an inductive predicate `P`, its introduction rules typically have
the form `∀⋯, ⋯ → P ⋯` and can be used to prove goals of the form `⊢ P ⋯`

Elimination works the other way around. It extracts information from a theorem
or hypothesis of the form `P ⋯`, Elimination takes various forms: pattern
matching, the `cases` and `induction` tactics, and custom elimination rules
(e.g., `And.left`).

* `cases` works like `induction` but without induction hypothesis.

* `match` is available as well.

Now we can finally understand how `cases h` where `h : l = r` work
and how `cases Classical.em h` work.  -/

theorem cases_Eq_example {α : Type} (l r : α) (h : l = r) (P : α → α → Prop) :
  P l r := by
  cases h
  -- replaced r with l everywhere
  sorry

theorem cases_Classical_em_example {α : Type} (a : α) (P Q : α → Prop) :
  Q a := by
  have hor : P a ∨ ¬ P a := Classical.em (P a)
  cases' hor with hl hr
  . sorry
  . sorry
  -- broke ∨ into cases.
  done

theorem Star_Star_iff_Star {α : Type} (R : α → α → Prop) (a b : α) :
  Star (Star R) a b ↔ Star R a b := by
  constructor
  { intro h
    induction h with
    | base a b hab => sorry
    | refl a => sorry
    | trans a b c hab hbc ihab ihbc =>
      -- TODO: More on monday...
      sorry
  }
  { sorry }
  done
