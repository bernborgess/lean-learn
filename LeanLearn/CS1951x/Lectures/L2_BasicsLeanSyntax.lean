

opaque α : Type
opaque β : Type
opaque γ : Type

def someFunOfType : (α → β → γ) → ((β → α) → β) → α → γ :=
  λ f => λ g => λ a => f a (g (λ _ => a))
