
def fst : α × β → α
| ⟨a,_⟩ => a

variable {α : Type}
variable {β : Type}

def transformType : β → (α = β) → α
| b,h => cast h.symm b
