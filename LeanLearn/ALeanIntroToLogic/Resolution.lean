
#check 1 + 1

#check Or.elim

theorem resolution : (p ∨ q) ∧ (¬p ∨ r) → q ∨ r := by
    intro h
    by_cases hp : p
    .   apply Or.elim h.2
        .   intro np; contradiction
        .   intro hr; right; assumption
    .   apply Or.elim h.1
        .   intro hpp; contradiction
        .   intro hq; left; assumption
