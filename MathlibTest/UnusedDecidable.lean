import Mathlib.Tactic.Linter.UnusedDecidable

set_option linter.unusedDecidable true

#check Lean.Elab.Command.Context

set_option Elab.inServer true

set_option Elab.inServer true


/-- foo -/
theorem foo [DecidableEq α] : True := True.intro
