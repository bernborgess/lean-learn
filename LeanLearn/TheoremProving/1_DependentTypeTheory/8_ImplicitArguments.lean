-- Implicit Arguments
universe u
def Lst (α : Type u) : Type u := List α
def Lst.cons (α : Type u) (a : α) (as : Lst α) : Lst α := List.cons a as
def Lst.nil (α : Type u) : Lst α := List.nil
def Lst.append (α : Type u) (as bs : Lst α) : Lst α := List.append as bs
#check Lst          -- Type u_1 → Type u_1
#check Lst.cons     -- (α : Type u_1) → α → Lst α → Lst α
#check Lst.nil      -- (α : Type u_1) → Lst α
#check Lst.append   -- (α : Type u_1) → Lst α → Lst α → Lst α

#check Lst.cons _ 0 (Lst.nil _)

def as : Lst Nat := Lst.nil _
def bs : Lst Nat := Lst.cons _ 5 (Lst.nil _)

#check Lst.append _ as bs

def ident {α : Type u} (x : α) := x

#check ident
#check ident 1
#check ident "hello"
#check @ident

section
  variable {α : Type u}
  variable (x : α)
  def ident' := x
end

#check ident' "Hello"


