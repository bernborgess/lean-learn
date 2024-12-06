
variable (g : Nat → Nat → Nat)
variable (hg : g 0 0 = 0)

theorem gex1 :  ∃ x, g x x = x := ⟨0, hg⟩  
theorem gex2 :  ∃ x, g x 0 = x := ⟨0, hg⟩  
theorem gex3 :  ∃ x, g 0 0 = x := ⟨0, hg⟩  
theorem gex4 :  ∃ x, g x x = 0 := ⟨0, hg⟩  

set_option pp.explicit true -- display implicit arguments
#print gex1
#print gex2
#print gex3
#print gex4

-- Elim example
variable (α : Type) (p q : α → Prop)

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  Exists.elim h 
    (λ w : α =>
     λ hw : p w ∧ q w =>
     show ∃ x, q x ∧ p x from ⟨w, hw.right, hw.left⟩ 
    )

-- using match
example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with
  | ⟨w, hpw, hqw⟩ => ⟨w, hqw, hpw⟩ 

-- using let
example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  let ⟨w, hpw, hqw⟩ := h
  ⟨w, hqw, hpw⟩ 

-- using implicit match
example : (h : ∃ x, p x ∧ q x) → ∃ x, q x ∧ p x :=
  fun ⟨w, hpw, hqw⟩ => ⟨w, hqw, hpw⟩ 

