module

import Lean
public import Mathlib.Cafe.Module.Meta0
import Mathlib.Cafe.Repr

open Lean
run_cmd do
  let some c := (← getEnv).find? ``foo | throwError "Couldn't find it!"
  logInfo m!"{repr c}"

set_option trace.Compiler.result true

public meta def bar (n : Nat) : (fun _ b => b) foo Nat := (n + 1)
-- ^ law: Must accommodate both meta imports and imports of this file downstream
-- Goal: meta import should only be necessary downstream when I want to use non-meta defs in the meta phase. And when we do include it, we are therefore loading all the IR we need

-- Question: when should we really do meta imports? Is it really only when lifting non-meta to meta? Or are there benefits when we only require the meta parts due to inserting a hygiene barrier?
-- What are the real costs/benefits to meta defs vs. regular defs + meta imports?
-- SQ: why are meta defs allowed in the types of non-meta defs and vice versa?
-- SQ: what did he mean by "get rid of inline restriction"

-- No matter what path you take to a downstream module, these^[what?] will be bound together: have all or lose all

/-
import Mathlib.Cafe.Module.Meta

-/
