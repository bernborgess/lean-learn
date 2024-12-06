import Mathlib.Init.Set
open Classical
#check And.elim

theorem t2 (Δ : Set Prop) (A B M : Prop)
  (h : A = ¬B)
  (hdcomplete : ∀x, ((¬x) ∉ Δ) → ((x) ∈ Δ))
  (hi : (M → B) ↔ (B ∈ Δ))
  : (M → ¬B) ↔ ((¬B) ∈ Δ) := by
  constructor
  . intro (hmnb : M → ¬B)
    apply byContradiction
    intro (hbnd : (¬B) ∉ Δ)
    have hbind : B ∈ Δ := hdcomplete B hbnd
    have hmib : M → B := hi.mpr hbind


    -- contradiction

    -- intro (hbnd : (¬B) ∉ Δ)

    sorry

  . sorry
  done
