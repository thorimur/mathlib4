module

import Lean
import Mathlib.Cafe.Repr
import Lake

def foo (n : Nat) := n + 5

@[expose] public def pubFoo (n : Bool) := n && n


-- Private bodies allow you to change the implementation and control the interface
-- Your API is the type + lemmas defining interaction with the rest of the library
--

-- open Lean
-- run_cmd do
--   let some c := (← getEnv).find? ``pubFoo | throwError "Couldn't find it!"
--   logInfo m!"{repr c}"
