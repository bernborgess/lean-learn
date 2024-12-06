import Lean
import Std.Tactic.Basic

/-! # Metaprogramming

User can extend Lean with custom tactics and tools. This kind of
programming-programming the prover is called `metaprogramming`.

Lean's metaprogramming framework uses mostly the same notions and syntax as
Lean's input language itself. Abstract syntax trees __reflect__ internal data
structures, e.g. for expressions (terms). The prover's internals are exposed
through Lean interfaces, which we can use for:

* acessing the current context and goal;
* unifying expressions;
* querying and modifying the environment;
* setting attributes.

Most of Lean itself is implemented in Lean.

Example applications:

* proof goal transformations;
* heuristic proof search;
* decision procedures;
* definition generators;
* advisor tools;
* exporters;
* ad hoc automation.

Advantages of Lean's metaprogramming framework:

* Users do not need to learn another programming language to write
  metaprograms; they can work with the same constructs and notation used to
  define ordinary objects in the prover's library.

* Everything in that library is available for metaprogramming purposes.

* Metaprograms can be written and debugged in the same intractive environment,
  encouraging a style where formal libraries and supporting automation are
  developed at the same time.

-/

open Lean Lean.Meta Lean.Elab.Tactic Lean.TSyntax

-- 16:00

/-! ## Tactic Combinators

When programming our own tactic, we often need to repeat some actions on
several goals, or to recover if a tactic fails. Tactic combinators help in
such cases.

`repeat` applies its argument repeatedly on all (sub...sub)goals until it cannot
be applied any further.  -/

inductive Even : Nat → Prop where
  | zero : Even 0
  | add_two : ∀ k : Nat, Even k → Even (k + 2)

theorem repeat_example :
  Even 4 ∧ Even 2 ∧ Even 0 := by

  repeat' apply And.intro
  repeat' apply Even.add_two
  repeat' apply Even.zero

  done

-- 17:12

-- all_goals applies its argument once to each goal

-- try transforms its argument into a tactic that never fails
theorem all_goals_try_example :
  Even 4 ∧ Even 7 ∧ Even 3 ∧ Even 0 :=
  by
    repeat' apply And.intro
    all_goals try repeat' apply Even.add_two
    all_goals try apply Even.zero
    repeat sorry
    done

-- `solve | ... | ... | ...` is like `first` exept that is succeed only if one of the
-- arguments fully proves the current goal`


-- try transforms its argument into a tactic that never fails
theorem all_goals_solve_example :
  Even 4 ∧ Even 7 ∧ Even 3 ∧ Even 0 :=
  by
    repeat' apply And.intro
    any_goals
      solve
      | repeat'
          first
            | apply Even.add_two
            | apply Even.zero
    repeat sorry
    done


-- ## Macros

/- We start with the actual metaprogramming, by conding a custom tactic as a
macro. The tactic embodies the behavior we hardcoded in the `solve` example
above: -/

macro "intro_and_even" : tactic =>
  `(tactic|
      (repeat' apply And.intro
       any_goals
        solve
        | repeat'
            first
            | apply Even.add_two
            | apply Even.zero))

-- Let's apply our custom tactic:
theorem intro_and_even_example :
  Even 4 ∧ Even 7 ∧ Even 3 ∧ Even 0 :=
  by
    intro_and_even
    repeat' sorry
    done

/-! ## The Metaprogramming Monads

`MetaM` is the low-level metaprogramming monad. `TacticM` extends `MetaM` with
goal management.

* `MetaM` is a state monad providing access to the global context (including all
  definitions and inductive types), notations, and attributes (e.g., the list of
  `@[simp]` theorems), among others. `TacticM` additionally provides access to
  the list of goals.

* `MetaM` and `TacticM` behave like an option monad. The metaprogram `failure`
  leaves the monad in an error state.)

* `MetaM` and `TacticM` support tracing, so we can use `logInfo` to display messages.

* Like other monads, `MetaM` and `TacticM` support imperative constructs such as
  `for`-`in`, `continue`, and `return`.  -/

def traceGoals : TacticM Unit := do
  -- logInfo m!"Lean version {Lean.versionString}"
  -- logInfo "All goals:"
  let goals ← getUnsolvedGoals
  logInfo m!"{goals.length} goals: {goals}"
  match goals with
  | []     => return
  | _ :: _ =>
    let target ← getMainTarget -- The type we are trying to show.
    logInfo m!"First goal's target: {target}"

elab "trace_goals" : tactic => traceGoals

example : 1 + 1 = 2 := by
  trace_goals
  rfl
  done

theorem Even2_and_Even0 : Even 20 ∧ Even 0 := by
  trace_goals
  intro_and_even
  done

#print Even2_and_Even0

-- 1:08:00

/-! ## First Example: An Assumption Tactic

We define a `hypothesis` tactic that behaves essentially the same as the
predefined `assumption` tactic -/

def hypothesis : TacticM Unit :=
  withMainContext do
    let target ← getMainTarget
    let lctx ← getLCtx
    for ldecl in lctx do
      if ldecl.isImplementationDetail then continue
      -- ? Element of the context is exactly our goal?
      let eq ← isDefEq ldecl.type target
      if !eq then continue
      let goal ← getMainGoal
      -- * Close the goal with this element as an expression
      goal.assign ldecl.toExpr
      return
    failure

elab "hypothesis" : tactic => hypothesis

theorem hypothesis_example {α : Type} {p : α → Prop} {a : α} (hpa : p a)
  : p a := by
  hypothesis
  done
