-- Local Definitions
#check let y := 2 + 2; y * y   -- Nat
#eval  let y := 2 + 2; y * y   -- 16

def twice_double (x : Nat) : Nat :=
  let y := x + x; y * y

#eval twice_double 2   -- 16

-- You can combine multiple assignments by chaining let statements:

#check let y := 2 + 2; let z := y + y; z * z   -- Nat
#eval  let y := 2 + 2; let z := y + y; z * z   -- 64

-- The ; can be omitted when a line break is used.

def t (x : Nat) : Nat :=
  let y := x + x
  y * y

-- As an exercise, try to understand why the definition of foo below
-- type checks, but the definition of bar does not.

def foo := let a := Nat; fun x : a => x + 2
#check foo

-- Meaning of notation `x + 2` is `type dependent`
-- def bar := (fun a => fun x : a => x + 2) Nat

