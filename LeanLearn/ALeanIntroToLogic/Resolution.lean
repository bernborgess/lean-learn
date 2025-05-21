
theorem resolution : (p ∨ q) ∧ (¬p ∨ r) → q ∨ r := by
    intro h
    by_cases hp : p
    .   apply Or.elim h.2
        .   intro np; contradiction
        .   intro hr; right; assumption
    .   apply Or.elim h.1
        .   intro hpp; contradiction
        .   intro hq; left; assumption

theorem monitor {p q r : Prop}: (p → (q ∨ r)) → ((p → q) ∨ (p → r)) :=
    λ f => Or.elim (Classical.em p)
    (λ hp => Or.elim (f hp)
                (λ hq => Or.inl (λ _ => hq))
                (λ hr => Or.inr (λ _ => hr)))
    (λ hnp => Or.inl (λ hp => absurd hp hnp))

theorem hometactic {p q r : Prop}: (p → (q ∨ r)) → ((p → q) ∨ (p → r)) := by
    intro f
    apply Or.elim (Classical.em p)
    . intro (hp : p)
      apply Or.elim (f hp)
      . intro (hq : q)
        apply Or.inl
        intros
        exact hq
      . intro (hr : r)
        apply Or.inr
        intros
        exact hr
    . intro (hnp : ¬p)
      apply Or.inl
      intro hp
      contradiction
