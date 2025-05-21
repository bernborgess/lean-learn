import Mathlib.Algebra.BigOperators.Group.Finset.Defs
open BigOperators

-- Example: n ≥ 1 ⇒ 2 + 22 + 23 + … + 2n = 2n+1 - 2
example : 1 + 1 = 2 := by rfl

#eval ∑ x ∈ {1,2,3,16}, x

-- example n : (n ≥ 1) → ∑ i ∈ {x : ℕ | x ≤ n}, 2^i = 2^(n+1) - 2 := sorry

#eval ∑ x ∈ (Finset.range 8), x

def theSet n := {x:ℕ | 1 ≤ x ∧ x ≤ n}
#check theSet 3

-- example : (∑ x ∈ {1,2,3}, 2^x) = 2^(4) - 1 := by
--   simp
--   apply?
--   done
