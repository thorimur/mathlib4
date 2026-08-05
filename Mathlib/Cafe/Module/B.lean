module

import Mathlib.Cafe.Module.A
import Lean
import Mathlib.Cafe.Repr



open Lean

set_option backward.proofsInPublic true

#check Environment

run_cmd do
  let env ← getEnv
  withExporting do

  logInfo m!"{(← getEnv).isExporting}"
  let c ← getConstInfo ``foo_eq
  let a := wasOriginallyTheorem (← getEnv) ``foo_eq
  logInfo m!"{repr c}"

theorem foo_eq' : foo 5 = 6 := by rfl
