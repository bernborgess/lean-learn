import Mathlib.Init.Set

/- ## Introductory Example

Consider the following programming task:

    Implement a function `sum257 ns` that sums up the second, fifth, and
    seventh items of a list `ns` of natural numbers. Use `Option ℕ` for the
    result so that if the list has fewer than seven elements, you can return
    `Option.none`.

A straightforward solution follows: -/

def sum257 (ns : List Nat) : Option Nat :=
match ns.take 7 with
| [_,t,_,_,f,_,s] => some $ t + f + s
| _ => none

def sum257₂ (ns : List Nat) : Option Nat := do
  let t ← ns.get? 1
  let f ← ns.get? 4
  let s ← ns.get? 6
  t + f + s

-- 32min

-- ## A Type Class of Monads

-- Monads are a mathematical structure, so we use class to add them as a type
-- class. We can think of a type class as a structure that is parameterized by a
-- type, or here, by a type constructor `m : Type → Type`. -/

class LawfulMonadC (m : Type → Type)
  extends Pure m, Bind m where
  pure_bind {α β : Type} (a : α) (f : α → m β) :
    (pure a >>= f) = f a
  bind_pure {α : Type} (ma : m α) :
    (ma >>= pure) = ma
  bind_assoc {α β γ : Type} (f : α → m β) (g : β → m γ)
      (ma : m α) :
    ((ma >>= f) >>= g) = (ma >>= (fun a ↦ f a >>= g))

-- ## No Effects
-- Our first monad is the trivial monad `m := id`
-- i.e. `m := (fun α ↦ α)`

def id.pure {α : Type} : α → id α
| a => a

def id.bind {α β : Type} : id α → (α → id β) → id β
| a, f => f a


instance id.LawfulMonadC : LawfulMonadC id :=
  { pure := id.pure
    bind := id.bind
    pure_bind := by
      intro α β a f
      rfl
    bind_pure := by
      intro α ma
      rfl
    bind_assoc := by
      intro α β γ f g ma
      rfl
  }


/- ## Mutable State

The state monad provides an abstraction corresponding to a mutable state. Some
compilers recognize the state monad to produce efficient imperative code. -/

def Action (σ α : Type) : Type :=
  σ → α × σ

def Action.read {σ : Type} : Action σ σ
  | s => (s, s)

def Action.write {σ : Type} (s : σ) : Action σ Unit
  | _ => ((), s)

def Action.pure {σ α : Type} (a : α) : Action σ α
  | s => (a, s)

def Action.bind {σ α β : Type} (ma : Action σ α) (f : α → Action σ β) : Action σ β
  | s => match ma s with
    | (a, s') => f a s'

/- `Action.pure` is like a `return` statement; it does not change the state.

`Action.bind` is like the sequential composition of two statements with
respect to a state. -/

instance Action.Monad {σ : Type} :
  Monad (Action σ) :=
  { pure       := Action.pure
    bind       := Action.bind }

def increasingly : List Nat → Action Nat (List Nat)
  | []        => pure []
  | (n :: ns) => do
    let prev ← Action.read
    if n < prev then
      increasingly ns
    else
      Action.write n
      let ns' ← increasingly ns
      pure (n :: ns')

#eval increasingly [1, 2, 3, 2] 0
#eval increasingly [1, 2, 3, 2, 4, 5, 2] 0

-- 1:14

-- ## Nondeterminism

-- The set monad stores an arbitrary, possibly infinite
-- number of α values

#check Set

def Set.pure {α : Type} : α → Set α
| a => {a}

def Set.bind {α β : Type} : Set α → (α → Set β) → Set β
| A, f => {b | ∃a, a ∈ A ∧ b ∈ f a}

-- `Set.bind` is like a `map` function over sets in which each
-- element of the source set maps to a set of element (all of
-- which are combined).

instance Set.Monad : Monad Set :=
  { pure := Set.pure
    bind := Set.bind }
