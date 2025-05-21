import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Fin.Tuple.Reflection
open BigOperators

-- Example: n ≥ 1 ⇒ 2 + 22 + 23 + … + 2n = 2n+1 - 2
example : 1 + 1 = 2 := by rfl

#eval ∑ x ∈ {1,2,3,16}, x

example : (n ≥ 1) → 2 + 2^i = 2^(n+1) - 2 := sorry

-- abbrev iota (n : ℕ) := Fin n → ℕ

def f (x : Fin 3) : ℕ := 3 * x

def summer := ∑ i, f i

-- #eval ∑ i, f i
-- #eval Finset.range 9

#eval ∑ x ∈ (Finset.range 4), x

def lhs (n : ℕ) := ∑ i ∈ (Finset.range n), 2 ^ (i + 1)
#eval lhs 5
def rhs (n : ℕ) := 2^(n+1) - 2
#eval rhs 5

example (n : ℕ) : (n ≥ 1) → lhs n = rhs n := by
    intro hn
    induction' n with n h
    .   -- zero
        contradiction
    .   -- succ
        clear hn
        induction' n with n hh
        .   unfold lhs rhs ; simp
        simp at hh h
        simp_rw [h] at hh
        simp at hh
        -- ???
        sorry


def theSet n := {x:ℕ | 1 ≤ x ∧ x ≤ n}
#check theSet 3

-- example : (∑ x ∈ {1,2,3}, 2^x) = 2^(4) - 1 := by
--   simp
--   apply?
--   done
