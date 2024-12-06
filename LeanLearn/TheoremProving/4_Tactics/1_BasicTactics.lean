

example : ∀ a b c : Nat , a = b → a = c → c = b :=
  λ _ _ _ hab hac =>
  have hca := Eq.symm hac
  Eq.trans hca hab

example : ∀ a b c : Nat , a = b → a = c → c = b := by
  intro a b c hab hac
  exact Eq.trans (Eq.symm hac) hab

example : ∀ a b c : Nat , a = b → a = c → c = b := by
  intro a b c hab hac   -- c = b
  apply Eq.trans        -- c = ?b ; ?b = b  ; ?b : Nat
  apply Eq.symm         -- ?b = c ; ?b = b  ; ?b : Nat
  exact hac             -- set ?b := a, now prove a = b
  exact hab             -- exactly
  done

example : ∀ a b c : Nat , a = b → a = c → c = b := by
  intro a b c hab hac         -- (C) <-- (A) --> (B)
  have hca := Eq.symm hac     -- (C) --> (A) --> (B) with symm
  rw [hca,hab]
  done

example : ∀ a b c : Nat , a = b → c = b → c = a := by
  intro a b c hab hcb
  apply Eq.trans
  apply hcb
  apply Eq.symm
  apply hab
  done

example : ∀ a b c : Nat , a = b → c = b → c = a := by
  intro a b c hab hcb         -- (A) --> (B) <-- (C)
  rw [hab,hcb]
  done
