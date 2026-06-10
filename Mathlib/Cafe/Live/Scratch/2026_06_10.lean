module

public meta import Lean
public import ProofWidgets

/-- info: ProofWidgets.MakeEditLink : ProofWidgets.Component ProofWidgets.MakeEditLinkProps -/
#guard_msgs in
#check ProofWidgets.MakeEditLink


#check Lean.Meta.Tactic.TryThis.SuggestionStyle


#info_trees in
example : True := by exact True.intro

open Lean Elab Command Meta Tactic TryThis

elab tk:"#foo" : command => do
  let stx ← `(tactic| grind; simp; exact?)
  let msg ← liftCoreM <| Hint.mkSuggestionsMessage #["#check Bool"] tk none false
  logInfo m!"Our suggestion is: {msg}"
  liftCoreM <| addSuggestion tk {
    suggestion := stx,
    toCodeActionTitle? := fun s => "use " ++ s }

#foo

#check addSuggestion
