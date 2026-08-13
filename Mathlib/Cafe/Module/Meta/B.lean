module

import Mathlib.Cafe.Module.Meta.A
import Lean.Elab.Command

open Lean
run_cmd
  -- logInfo m!"{isMarkedMeta (← getEnv) ``bar}"
  -- logInfo m!"{repr <| getIRPhases (← getEnv) ``bar}"
  logInfo m!"{isDeclMeta (← getEnv) ``bar}"

#check foo 5
