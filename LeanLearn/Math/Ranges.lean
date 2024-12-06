import Mathlib.Data.Nat.Defs

def caps10 {x:ℕ} (_ : x < 20) : ℕ :=
  if x > 10 then 10 else x

def noCap {x:ℕ} (_ : x >= 20) : ℕ :=
  x

def mayCaps10 (x : ℕ) : ℕ :=

  -- let ory := Nat.lt_or_ge x 20
  -- if let Or.inl h := ory then 3 else 0
  -- match ory with
  -- | Or.inl h => x
  -- | Or.inr h => x


  -- match (Nat.lt_or_ge x 20) with
  -- | Or.inl h => 3
  -- | Or.inr h => 3

  -- let h : (x < 20) ∨ (x >= 20) := Nat.lt_or_ge x 20
  -- 3
  if h : x < 20 then
    caps10 h
  else if h : x >= 20 then
    noCap h
  else 0

#eval mayCaps10 19
