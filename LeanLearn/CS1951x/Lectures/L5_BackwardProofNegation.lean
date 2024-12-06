import Mathlib.Tactic.Linarith
import Mathlib.Data.Nat.Basic

namespace BackwardProofs

theorem Not_Not_intro (a : Prop) : a → ¬¬ a := by
    intro ha hna
    contradiction
    done

theorem Exists_double_iden : ∃ n : ℕ, 2 * n = n := by
    apply Exists.intro 0
    rfl
    done

theorem not_Exists_double_lt : ¬ ∃ n : ℕ, 2 * n < n := by
    intro hex
    apply Exists.elim hex
    intro n hn
    linarith
    done


theorem add_zero (n : ℕ) : 0 + n = n := by
    induction n with
    | zero      => rfl
    | succ n'   => simp
    done

/- Cleanup Tactics

`clear` removes unused variables or hypotheses.

`rename` changes the name of a variable or hypotesis.  -/

theorem cleanup_example (a b c : Prop) (ha : a) (hb : b)
    (hab : a → b) (hbc : b → c) : c := by
    clear ha hab a  -- not used in the proof
    apply hbc
    clear hbc c     -- not needed anymore
    rename b => h   -- hb is verbose, use h
    exact h
    done

end BackwardProofs
