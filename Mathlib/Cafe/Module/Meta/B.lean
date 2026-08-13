module

public meta import Mathlib.Cafe.Module.Meta.A
import Lean.Elab.Command

open Lean

set_option trace.Compiler.result true


meta def barUsingBar := bar

public meta def bar' := barUsingBar



-- public
run_cmd
  -- logInfo m!"{isMarkedMeta (← getEnv) ``bar}"
  -- logInfo m!"{repr <| getIRPhases (← getEnv) ``bar}"
  logInfo m!"{isDeclMeta (← getEnv) ``bar}"
  logInfo m!"{isDeclMeta (← getEnv) ``bar}"

#check foo 5
