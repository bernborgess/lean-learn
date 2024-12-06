import Mathlib.Data.Nat.Basic

variable (α β γ: Type)

/- # FPV Lab 1: Definitions and Statements

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe

/- ## Question 1: Terms

Complete the following definitions by replacing the `sorry` markers with terms
of the expected type.

Hint: A procedure for doing so systematically is described in Section 1.4 of
the Hitchhiker's Guide. As explained there, you can use `_` as a placeholder
while constructing a term. By hovering over `_`, you will see the current
logical context. -/

def I : α → α :=
    λ a => a

def K : α → β → α :=
    λ a => λ _ => a

def C : (α → β → γ) → β → α → γ :=
    λ f => λ b => λ a => f a b

def projFst : α → α → α :=
    λ a => λ _ => a

/- Give a different answer than for `projFst`. -/

def projSnd : α → α → α :=
    λ _ => λ a => a

def someNonsense : (α → β → γ) → α → (α → γ) → β → γ :=
    λ _ => λ a => λ f => λ _ => f a

/- ## Question 2: Typing Derivation

Show the typing derivation for your definition of `C` above, on paper or using
ASCII or Unicode art. You might find the characters `–` (to draw horizontal
bars) and `⊢` useful. -/

-- Write your solution in a comment here or on paper
/-

–––––––––––––––––––––––––– Var –––––––––––––––––––––– Var
[f:α→β→γ, b:β, a:α] ⊢ f:α→β→γ  [f:α→β→γ, b:β, a:α] ⊢ a:α
––––––––––––––––––––––––––––––––––––––––––––––––––––– App  ––––––––––––––––––––– Var
[f:α→β→γ, b:β, a:α] ⊢ f a : β → γ                          [f:α→β→γ, b:β, a:α] ⊢ b:β
–––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––– App
[f:α→β→γ, b:β, a:α] ⊢ f a b : γ
––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––– Fun
[f:α→β→γ, b:β] ⊢ λ a:α => f a b : α → γ
––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––– Fun
[f:α→β→γ] ⊢ λ b:β => λ a:α => f a b : β → α → γ
––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––– Fun
[] ⊢ λ f:α→β→γ => λ b:β => λ a:α => f a b : (α → β → γ) → β → α → γ
-/

/- ## Question 3: Arithmetic Expressions

Consider the type `AExp` from the lecture and the function `eval` that
computes the value of an expression. You will find the definitions in the file
`LoVe02_ProgramsAndTheorems_Demo.lean`. One way to find them quickly is to

1. Hold down the Control (on Linux and Windows) or Command (on macOS) key,
2. Move the cursor to the identifier `AExp` or `eval`, and
3. Click the identifier.
-/


/- ### Arithmetic Expressions -/

inductive AExp : Type where
  | num : ℤ → AExp
  | var : String → AExp
  | add : AExp → AExp → AExp
  | sub : AExp → AExp → AExp
  | mul : AExp → AExp → AExp
  | div : AExp → AExp → AExp

def eval (env : String → ℤ) : AExp → ℤ
  | AExp.num i     => i
  | AExp.var x     => env x
  | AExp.add e₁ e₂ => eval env e₁ + eval env e₂
  | AExp.sub e₁ e₂ => eval env e₁ - eval env e₂
  | AExp.mul e₁ e₂ => eval env e₁ * eval env e₂
  | AExp.div e₁ e₂ => eval env e₁ / eval env e₂


#check AExp
#check eval

/- 3.1. Test that `eval` behaves as expected. Make sure to exercise each
constructor at least once. You can use the following environment in your tests.
What happens if you divide by zero?

Note that `#eval` (Lean's evaluation command) and `eval` (our evaluation
function on `AExp`) are unrelated. -/

def someEnv : String → ℤ
  | "x" => 3
  | "y" => 17
  | _   => 201

#eval eval someEnv (AExp.var "x")   -- expected: 3
-- invoke `#eval` here
section
open AExp

#eval eval someEnv (num 42)

#eval eval someEnv (add (num 42) (var "z"))

#eval eval someEnv (sub (num 42) (num 43))

#eval eval someEnv (mul (num 1) (num 0))

#eval eval someEnv (div (num 1) (num 0))


/- 3.2. The following function simplifies arithmetic expressions involving
addition. It simplifies `0 + e` and `e + 0` to `e`. Complete the definition so
that it also simplifies expressions involving the other three binary
operators. -/

def simplify : AExp → AExp
  | add (num 0) e₂ => simplify e₂
  | add e₁ (num 0) => simplify e₁
  -- insert the missing cases here
  | sub e₁ (num 0) => simplify e₁

  | mul (num 1) e₂ => simplify e₂
  | mul e₁ (num 1) => simplify e₁

  | mul (num 0) _  => num 0
  | mul _ (num 0)  => num 0

  | div e₁ (num 1) => simplify e₁
  | div _ (num 0)  => num 0
  -- catch-all cases below
  | num i               => num i
  | var x               => var x
  | add e₁ e₂           => add (simplify e₁) (simplify e₂)
  | sub e₁ e₂           => sub (simplify e₁) (simplify e₂)
  | mul e₁ e₂           => mul (simplify e₁) (simplify e₂)
  | div e₁ e₂           => div (simplify e₁) (simplify e₂)

end

/- 3.3. Is the `simplify` function correct? In fact, what would it mean for it
to be correct or not? Intuitively, for `simplify` to be correct, it must
return an arithmetic expression that yields the same numeric value when
evaluated as the original expression.

Given an environment `env` and an expression `e`, state (without proving it)
the property that the value of `e` after simplification is the same as the
value of `e` before. -/

theorem simplify_correct (env : String → ℤ) (e : AExp) :
  ∀ e : AExp, e = simplify e :=
  sorry

/-! ## Question 4: Lists and Options

Another common inductive datatype in functional programming is the `Option`
type. Intuitively, an `Option α` is a "possibly-empty container" that either
holds a single value of type `α` or is "empty." The type is defined as follows:

  inductive Option (α : Type)
  | none           : Option α
  | some (val : α) : Option α

We can pattern-match on options just as we do on `List`s or `AExp`s.

Here are some examples of options: -/

#check (none : Option Nat)
#check (none : Option Bool)
#check some "hello"
#check some 14
#check some (λ x => 2 * x)

/-! 4.1. Declare a function `omap : (α → β) → List (Option α) → List (Option β)`
that applies a provided function to every non-"empty" element of a list of
options. In other words, given a function `f` and list `xs`, `omap` should take
every element of `xs` of the form `some x` to the element `some (f x)` in the
output; and it should take every element of `xs` of the form `none` to `none` in
the output. Here's an example:

`omap (λ x => x + 1) [some 0, none, some 2] = [some 1, none, some 3]` -/

def omap {α β : Type} (f : α → β) : List (Option α) → List (Option β)
  := (List.map ∘ Option.map) f

#eval omap (λ x => x+1) [some 0, none, some 2]

/-! 4.2. State as Lean theorems (without proving them) the so-called functorial
properties of `omap`, which are stated informally below:

- `omap`ping the identity function over a list gives back that same list.
- `omap`ping the composition of two functions `g` and `f` over a list gives the
  same result as first `omap`ping `f` over that list and then `omap`ping `g`
  over the result.

Try to give meaningful names to your theorems, and make sure to state them
as generally as possible. You can enter `sorry` in lieu of a proof. -/

-- Write your theorem statements here
theorem omap_id_is_id : ∀ xs : List (Option α), omap id xs = xs
    := sorry

theorem omap_compose_is_compose_omap : ∀ f : β → γ, ∀ g : α → β, omap (f ∘ g) = (omap f) ∘ (omap g)
    := sorry
