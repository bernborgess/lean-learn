-- Calculational Proofs

variable
  (a b c d e : Nat)
  (h1 : a = b)
  (h2 : b = c + 1)
  (h3 : c = d)
  (h4 : e = 1 + d)

theorem T : a = e :=
  calc
    a = b     := h1
    _ = c + 1 := h2
    _ = d + 1 := congrArg Nat.succ h3
    _ = 1 + d := Nat.add_comm d 1
    _ = e     := Eq.symm h4

-- "Teaching" calc - implementing a custom calc 

def divides (x y : Nat) : Prop :=
  ∃ k, k*x = y 

def divides_trans (h₁ : divides x y) (h₂ : divides y z) : divides x z :=
  let ⟨k₁,d₁⟩ := h₁ 
  let ⟨k₂,d₂⟩ := h₂
  have aux1 : z = k₂ * y                  := Eq.symm d₂
  have aux2 : y = k₁ * x                  := Eq.symm d₁
  have aux3 : k₂ * y = k₂ * (k₁ * x)      := congrArg (λ x => k₂ * x) aux2
  have aux4 : k₂ * k₁ * x = k₂ * (k₁ * x) := Nat.mul_assoc k₂ k₁ x
  have aux5 : k₂ * (k₁ * x) = k₂ * k₁ * x := Eq.symm aux4
  have aux6 : k₂ * y = k₂ * k₁ * x        := Eq.trans aux3 aux5
  have aux7 : z = k₂ * k₁ * x             := Eq.trans aux1 aux6
  have d₃   : k₂ * k₁ * x = z             := Eq.symm aux7
  ⟨k₂ * k₁, d₃⟩ 

def divides_trans2 (h₁ : divides x y) (h₂ : divides y z) : divides x z :=
  let ⟨k₁,d₁⟩ := h₁ 
  let ⟨k₂,d₂⟩ := h₂

  have aux2 : y = k₁ * x                  := Eq.symm d₁
  have aux3 : k₂ * y = k₂ * (k₁ * x)      := congrArg (λ x => k₂ * x) aux2
  have aux4 : k₂ * k₁ * x = k₂ * (k₁ * x) := Nat.mul_assoc k₂ k₁ x

  have aux5 : k₂ * (k₁ * x) = k₂ * k₁ * x := Eq.symm aux4

  have aux6 : k₂ * y = k₂ * k₁ * x        := Eq.trans aux3 aux5
  have aux7 : k₂ * k₁ * x = k₂ * y        := Eq.symm aux6

  have aux7 : k₂ * k₁ * x  = z            := Eq.trans aux7 d₂ 

  ⟨k₂ * k₁, aux7⟩ 


