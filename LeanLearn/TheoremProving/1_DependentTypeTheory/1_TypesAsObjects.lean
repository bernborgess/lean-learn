-- try it 
def α : Type := Nat
def β : Type := Bool
-- def F : Type → Type := List
def F := List
def G : Type → Type → Type := Prod

def NatList := F Nat
def xs : NatList := [1,2,3]
#eval xs

#check α        -- Type
#check F α      -- Type
#check F Nat    -- Type
#check G α      -- Type → Type
#check G α β    -- Type
#check G α Nat  -- Type

#check trivial
#check True
#check Prop

#check true
#check Bool

#check fun n => Fin n
#check Nat → Type
#check Type 1

#check fun (_ : Type) => Type
#check Type → Type 1
#check Type 2


#check Type
#check Type 1

#check Type
#check Type 32
-- maximum universe level offset threshold (32) has been
-- reached, you can increase the limit using option
-- `set_option maxUniverseOffset <limit>`,

#check List
#check Prod

-- universe u
-- def F' (α : Type u) : Type u := Prod α α 

def F'.{u} (α : Type u) : Type u := Prod α α 

#check F'