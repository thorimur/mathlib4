import Lean
import Mathlib.Util.WhatsNew
import Mathlib.Cafe.Util

open Lean Expr

def myDef : Nat := 0 + 1

#print Expr

open Elab Tactic

#check LocalContext
#print LocalDecl
#check MetavarContext
#check MetaM
#check TermElabM

open Meta

variable (fvarId : FVarId)

syntax withPosition("foo" colGe "r") : command

  foo
r


macrox:ident ":" t:term " ↦ " y:term : term =>
  `(fun $x : $t => $y)

#check Parser.atomic⦃⦄

#eval (x : Nat) -- unexpected token 'elab'; expected '×', '×'' or '→', '->'

elab "my_tac" : tactic => do
  let g ← getMainGoal
  let type ← g.getType
  -- let (mvars, bis, t) ← do forallMetaTelescope type
  -- g.withContext do logInfo m!"{mvars}; {repr bis}; {t}"
  let funExpr ← forallTelescope type fun xs t₁ => do
    let (_, s) ← t₁.collectFVars.run {}
    logInfo m!"fvarIds: {s.fvarIds.map Expr.fvar}"
    mkForallFVars xs[0...1] t₁ (usedOnly := true)
  -- logInfo m!"got: {funExpr}"

set_option linter.unusedTactic false
nonrec theorem x : (e : Nat) → e = 3 := by
  -- refine fun (e : Nat) => ?m
  my_tac
