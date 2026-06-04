module

import Mathlib.Cafe.Live.Extensions.Init
import Lean

open Lean

#check ensureAttrDeclIsMeta

#check hasConst

run_cmd do
  modifyEnv fun env => nameLength.addEntry env `fooooooo

@[my_attr w, my_tag]
public def bar := true

def baz := false

run_cmd do
  let s := nameLength.getState (← getEnv)
  logInfo m!"{s.toArray}"
  logInfo m!"{A.myTagAttr.hasTag (← getEnv) `bar}"

-- #check PersistentEnvExtension.modifyState
-- #check PersistentEnvExtension.setState
