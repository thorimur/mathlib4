module


public import Mathlib.Cafe.Live.Extensions.Test1
import Lean
public import Batteries

open Lean

-- run_cmd do
--   let imported := nameLength.getModuleEntries (← getEnv)
--     ((← getEnv).getModuleIdx? `Mathlib.Cafe.Live.Extensions.Test1).get!
--   logInfo m!"{imported}"

run_cmd
  let s := nameLength.getState (← getEnv)
  logInfo m!"{s.toArray}"
