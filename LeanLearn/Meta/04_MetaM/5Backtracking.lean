import Lean
-- Backtracking
-- Many tactics naturally require backtracking:
-- the ability to go back to a previous state,
-- as if the tactic had never been executed.

-- A few examples:
-- `first | t | u` first executes t. If t fails, it backtracks and executes u.
-- `try t` executes t. If t fails, it backtracks to the initial state,
--    erasing any changes made by t.
-- `trivial` attempts to solve the goal using a number of simple tactics
--    (e.g. rfl or contradiction). After each unsuccessful application of such a tactic,
--    trivial backtracks.

-- Good thing, then, that Lean's core data structures are designed to enable easy
-- and efficient backtracking.

-- The corresponding API is provided by the `Lean.MonadBacktrack` class.
-- MetaM, TermElabM and TacticM are all instances of this class. (CoreM is not but could be.)

-- MonadBacktrack provides two fundamental operations:
-- `Lean.saveState : m s` returns a representation of the current state,
--    where m is the monad we are in and s is the state type.
--    E.g. for MetaM, saveState returns a Lean.Meta.SavedState containing the current environment,
--    the current MetavarContext and various other pieces of information.
-- `Lean.restoreState : s → m Unit` takes a previously saved state and restores it.
--    This effectively resets the compiler state to the previous point.

-- With this, we can roll our own MetaM version of the try tactic:

open Lean Meta Elab Tactic


def tryM (x : MetaM Unit) : MetaM Unit := do
  let s ← saveState
  try
    x
  catch _ =>
    restoreState s
