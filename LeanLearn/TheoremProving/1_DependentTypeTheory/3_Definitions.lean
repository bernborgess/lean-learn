-- Definitions
def double (x : Nat) : Nat :=
  x + x

#eval double 3 -- 6

def pi := 3.14159265

def add (x y : Nat) :=
  x + y

#eval add 3 2 -- 5

-- The parameter list can be separated
def add' (x : Nat) (y : Nat) :=
  x + y

#eval add' (double 3) (7 + 9) -- 22

def greater (x y : Nat) :=
  if x > y then x
  else y

def doTwice (f : α → α) (x : α) : α :=
  f (f x)

/-  fail to show termination for doNTimes
def doNTimes (n : Nat) (f : α → α) (x : α) : α := 
  if n == 0 then x
  else doNTimes (n - 1) f (f x)
#eval doNTimes 3 (λ x => x + 1) 0
-/

def compose (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : γ :=  
  g (f x)

#check compose

def square (x : Nat) : Nat :=
  x * x

#eval compose Nat Nat Nat double square 3 -- 18

def compose' (g : β → γ) (f : α → β) (x : α) : γ :=  
  g (f x)

#check compose'
