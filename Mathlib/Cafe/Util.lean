module

public import Lean
public meta import Mathlib.Lean.MessageData.ForExprs
public import Mathlib.Cafe.Repr

open Lean Elab Term Tactic Command


elab tk:"#show_stx" ppLine colGe cmd:command : command => do
  logInfoAt tk m!"{format cmd}"; elabCommand cmd
elab tk:"#show_stx!" ppLine colGe cmd:command : command => do
  logInfoAt tk m!"{repr cmd}"; elabCommand cmd

syntax (name := showTermStx) "#show_stx" colGe term : term
syntax (name := showTermStx!) "#show_stx!" colGe term : term
@[term_elab showTermStx] public meta def elabShowTermStx : TermElab := fun stx ty? => do
  logInfoAt stx[0] stx[1]; Term.elabTerm stx[1] ty?
@[term_elab showTermStx!] public meta def elabShowTermStx! : TermElab := fun stx ty? => do
  logInfoAt stx[0] stx[1]; Term.elabTerm stx[1] ty?

elab tk:"#show_stx" colGe tac:tactic : tactic => do
  logInfoAt tk m!"{format tac}"; evalTactic tac
elab tk:"#show_stx!" colGe tac:tactic : tactic => do
  logInfoAt tk m!"{repr tac}"; evalTactic tac

elab "#show_vars" : command => do
  logInfo m!"{(← getScope).varDecls}"

-- open Lean Meta Elab Parser PrettyPrinter Delaborator SubExpr Command

elab "#scopes" : command => do
  logInfo m!"{repr <|← getScopes}"

elab "#current_decls" : command => do
  let mut c := #[]
  for e@(decl, _) in (← getEnv).constants do
    unless (← getEnv).isImportedConst decl do
      c := c.push e
  logInfo m!"{repr c}"
