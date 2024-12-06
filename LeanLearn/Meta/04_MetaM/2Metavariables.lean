

example (n m : Nat) : n + m = m + n :=
  sorry

example {α} (a : α) (f : α → α) (h : ∀ a, f a = a) : f (f a) = a :=
  let x : (f (f a) = f a) := h (f a)
  let y : (f a = a) := h a
  show f (f a) = a from Eq.trans x y

example {α} (a : α) (f : α → α) (h : ∀ a, f a = a) : f (f a) = a := by
  apply Eq.trans
  apply h
  apply h
