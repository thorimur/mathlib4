module

import Mathlib.Cafe.Module.B
import Lean
import Mathlib.Cafe.Repr

open Lean

run_cmd do
  let some c := (← getEnv).find? ``pubFoo | throwError "Couldn't find it!"
  logInfo m!"{repr c}"

public theorem pubFoo_eq_true : true = true := by
  have := pubFoo
  sorry

-- @[expose]
-- public def pubBar (b : Bool) := pubFoo !b



/-
import A

#check pubFoo_eq_true

-/
