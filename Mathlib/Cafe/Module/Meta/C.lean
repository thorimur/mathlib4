module

public import Mathlib.Cafe.Module.Meta.InitA
public meta import Lean.Elab.Command

-- #foo

elab "#set_a" : command => do
  a.set (some true)

elab "#get_a" : command => do
  Lean.logInfo m!"{← a.get}"

#check Lean.Environment

#check Lean.enableInitializersExecution

#get_a

#set_a

#get_a
