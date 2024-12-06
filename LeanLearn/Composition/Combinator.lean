
def i   (x:α)                             := x

def k   (x:α) (y:β)                       := x

def ki  (x:α) (y:β)                       := y

def s   (f:α → β → γ) (g:α → β)           := λ x:α => f x (g x)

def b   (f:β → γ) (g:α → β)               := λ x:α => f (g x)

def c   (f:β → α → γ)                     := λ x:α => λ y:β => f y x

def w   (f:α → α → γ)                     := λ x:α => f x x

def d   (f:α → γ → δ) (g:β → γ)           := λ x:α => λ y:β => f x (g y)

def b₁  (f:γ → δ) (g:α → β → γ)           := λ x:α => λ y:β => f (g x y)

def ψ   (f:β → β → γ) (g:α → β)           := λ x:α => λ y:α => f (g x) (g y)

def φ   (f:α → β) (g:β → γ → δ) (h:α → γ) := λ x:α => g (f x) (h x)
