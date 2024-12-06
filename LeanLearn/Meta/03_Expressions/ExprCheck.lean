import Lean

open Lean

syntax (name := cmdElabTerm) "#elab " term : command
open Lean.Elab Lean.Elab.Command in
@[command_elab cmdElabTerm] def evalCmdElabTerm : CommandElab
  | `(#elab $term) => withoutModifyingEnv $ runTermElabM fun _ => do
    let e ← Term.elabTerm term none
    logInfo m!"{e} ::: {repr e}"
  | _ => throwUnsupportedSyntax

variable {p : Prop}

#elab p ∧ p

-- Get an expression for a term
#elab Type 6

#elab true

#elab fun y : Nat → Nat => y
