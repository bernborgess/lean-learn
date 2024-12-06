-- Variables and Sections
def compose (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)

def doTwice (α : Type) (h : α → α) (x : α) : α :=
  h (h x)

def doThrice (α : Type) (h : α → α) (x : α) : α :=
  h (h (h x))

-- Lean provides you with the variable command to make such
-- declarations look more compact:

variable (α β γ : Type)

def compose' (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)

def doTwice' (h : α → α) (x : α) : α :=
  h (h x)

def doThrice' (h : α → α) (x : α) : α :=
  h (h (h x))

-- You can declare variables of any type, not just Type itself:

section useful 
  variable (α β γ : Type)
  variable (g : β → γ) (f : α → β) (h : α → α)
  variable (x : α)

  def compose'' := g (f x)
  def doTwice'' := h (h x)
  def doThrice'' := h (h (h x))

  #print compose''
  #print doTwice''
  #print doThrice''
end useful

