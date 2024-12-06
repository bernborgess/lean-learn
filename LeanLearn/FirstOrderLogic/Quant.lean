
variable {F : α → Prop}

theorem t1 : (¬∃x,F x) → (∀x,¬ F x) := by
  intro hne x fx
  apply hne
  apply show ∃x, F x from ⟨x,fx⟩
  done

open Classical

#check em

theorem t2 : (¬∀x,F x) → (∃x,¬F x) := by

  intro hna
  apply byContradiction
  intro hnenf

  have ha : (∀x,F x) :=
    λ a => by
    cases (em (F a))
    . assumption
    . have hnfa : ¬F a := by assumption
      have hehe : (∃x,¬F x) := ⟨a,hnfa⟩
      apply absurd hehe hnenf
    done

  have henf : ∃x,¬F x := absurd ha hna
  apply absurd henf hnenf
  done
