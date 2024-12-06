-- Function Abstraction and Evaluation
#check fun (x : Nat) => x + 5   -- Nat → Nat
#check λ (x : Nat) => x + 5     -- λ and fun mean the same thing
#check fun x : Nat => x + 5     -- Nat inferred
#check λ x : Nat => x + 5       -- Nat inferred

#eval (λ x : Nat => x + 5) 10

def k := λ (x : Nat) (y : Bool) =>
  if not y
  then x + 1
  else x + 2

#eval k 1 True

def f (n : Nat) : String := toString n
def g (s : String) : Bool := s.length > 0

#check fun x : Nat => x
#check fun _ : Nat => true
#check fun x : Nat => g (f x) 
#check fun x => g (f x)

-- You can also pass types as parameters:
def ms := fun (α β γ : Type) (g: β → γ) (f : α → β) (x : α) => g (f x)
#eval ms Int String Bool (λ x => x.length > 0) (λ x => toString x) 4

 