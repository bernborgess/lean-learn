import Init.Data.Array.Basic
import Mathlib.Data.Nat.Basic

def x := Array.mkArray2 3 3

#print x


def Vec (n : Nat) (a : Type) := { ls : List a // ls.length = n }

def Vec.nil {α : Type} : Vec 0 α := ⟨[],rfl⟩

-- def Vec.cons : α → Vec n α → Vec (Nat.succ n) α
-- | a, ⟨v, h⟩ => ⟨a :: v, congrArg Nat.succ h⟩

def Vec.cons {α : Type} (a : α) (vn : Vec n α) : Vec (n + 1) α := by
  have ⟨v,h⟩ := vn
  have pan := congrArg (·+1) h
  exact ⟨a :: v,pan⟩
  done


section
open Vec
def m1 := cons 1 nil

def m2 := cons 2 $ cons 1 nil

def m3 := cons 3 $ cons 2 $ cons 1 nil

#reduce m3

end













inductive Disarray (α : Type) where
| nada : Disarray α
| c : α → Disarray α → Disarray α

section

open Disarray

def k : Disarray Nat := nada

def m : Disarray Nat := c 3 $ c 2 nada

#print m
end
