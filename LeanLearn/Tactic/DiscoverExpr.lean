import Lean

syntax (name := cmdElabTerm) "#elab " term : command

open Lean Elab Command in

@[command_elab cmdElabTerm] def evalCmdElabTerm : CommandElab
  | `(#elab $term) => withoutModifyingEnv $ runTermElabM fun _ => do
    let e ← Term.elabTerm term none
    logInfo m!"{e} ::: {repr e}"
  | _ => throwUnsupportedSyntax

#elab 1
