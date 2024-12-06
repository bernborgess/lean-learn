-- Exercises
-- 1. Prove these equivalences:
variable (α : Type) (p q : α → Prop)

def all_and_split : (∀ (x : α), p x ∧ q x) → (∀ (x : α), p x) ∧ (∀ (x : α), q x) :=
  λ ha =>
  have hap := λ x : α => (ha x).left
  have haq := λ x : α => (ha x).right
  ⟨hap, haq⟩

def and_all_split : ((∀ (x : α), p x) ∧ ∀ (x : α), q x) → ∀ (x : α), p x ∧ q x :=
  λ ⟨hap, haq⟩ => λ x =>
  ⟨hap x, haq x⟩

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
  Iff.intro
  (all_and_split α p q)
  (and_all_split α p q)

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
  λ hpq => λ hp => λ x =>
  (hpq x) (hp x)

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
  λ h => Or.elim h
  (λ hp => λ x => Or.inl (hp x))
  (λ hq => λ x => Or.inr (hq x))

-- You should also try to understand why the reverse implication is not
-- derivable in the last example.

-- 2. It is often possible to bring a component of a formula outside a universal
-- quantifier, when it does not depend on the quantified variable. Try proving
-- these (one direction of the second of these requires classical logic):

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : α → ((∀ _ : α, r) ↔ r) :=
  λ x => Iff.intro
  (λ h => h x)
  (λ r => λ _ => r)

open Classical

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

def all_imply_plus_arg : (∀ (x : α), r → p x) → r → ∀ (x : α), p x :=
  λ h => λ hr => λ x =>
    (h x) hr

def arg_plus_all_imply : (r → ∀ (x : α), p x) → ∀ (x : α), r → p x :=
  λ h => λ x => λ hr =>
    (h hr) x

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
  Iff.intro
  (all_imply_plus_arg α p r)
  (arg_plus_all_imply α p r)


-- 3. Consider the `barber paradox` that is, the claim that in a certain town
-- there is a (male) barber that shaves all and only the men who do not shave
-- themselves. Prove that this is a contradiction:

variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False :=
  byCases
  (λ s : shaves barber barber =>
    absurd s ((h barber).mp s))
  (λ ns =>
    absurd ((h barber).mpr ns) ns)


-- Remember that, without any parameters, an expression of type Prop is just
-- an assertion. Fill in the definitions of prime and Fermat_prime below, and
-- construct each of the given assertions. For example, you can say that there
-- are infinitely many primes by asserting that for every natural number n,
-- there is a prime number greater than n. Goldbach's weak conjecture states
-- that every odd number greater than 5 is the sum of three primes. Look up the
-- definition of a Fermat prime or any of the other statements, if necessary.

def even (n : Nat) : Prop :=
  ∃ k, 2 * k = n

example : even 8 :=
  ⟨4,rfl⟩

-- A prime number (or a prime) is a natural number greater than 1
-- that is not a product of two smaller natural numbers.
def prime (n : Nat) : Prop :=
  n > 1 ∧ ¬∃ x y, x < n ∧ y < n ∧ x * y = n

/-
example : prime 2 :=
  ⟨sorry,sorry⟩
-/

def infinitely_many_primes : Prop :=
  ∀ n : Nat, prime n → ∃ n', prime n' ∧ n < n'

-- In mathematics, a `Fermat number`, named after Pierre de Fermat,
-- the first known to have studied them, is a positive integer of the form
-- Fn = 2^(2^n) + 1
-- where n is a non-negative integer.
-- The first few Fermat numbers are:
-- 3, 5, 17, 257, 65537, 4294967297, 18446744073709551617, ...
-- (sequence A000215 in the OEIS).
-- If 2^k + 1 is prime and k > 0, then k itself must be a power of 2,
-- so 2^k + 1 is a Fermat number; such primes are called `Fermat primes`.
def Fermat_prime (n : Nat) : Prop :=
  ∃ k, k > 0 ∧ n = 2^k + 1 ∧ prime n

def infinitely_many_Fermat_primes : Prop :=
  ∀ n : Nat, Fermat_prime n → ∃ n', Fermat_prime n' ∧ n < n'

-- Goldbach's conjecture is one of the oldest and best-known unsolved problems
-- in number theory and all of mathematics. It states that every even natural
-- number greater than 2 is the sum of two prime numbers.
def goldbach_conjecture : Prop :=
  ∀ n : Nat, even n → 2 < n →
  ∃ p1 p2, prime p1 ∧ prime p2 ∧ p1 + p2 = n

-- Every odd number greater than 5 can be expressed as the sum of three primes
def Goldbach's_weak_conjecture : Prop :=
  ∀ n, ¬even n → 5 < n →
  ∃ p1 p2 p3, prime p1 ∧ prime p2 ∧ prime p3
  ∧ p1 + p2 + p3 = n

-- In number theory, Fermat's Last Theorem (sometimes called Fermat's conjecture,
-- especially in older texts) states that no three positive integers a, b, and c
-- satisfy the equation a^n + b^n = c^n for any integer value of n greater than 2.
-- The cases n = 1 and n = 2 have been known since antiquity to have infinitely many solutions

/-
def Fermat's_last_theorem : Prop :=
  ∀ n : Nat, 2 < n →
  ¬∃ a b c, a^n + b^n = c^n
-/


-- 5. Prove as many of the identities listed in the Existential Quantifier section as you can.
