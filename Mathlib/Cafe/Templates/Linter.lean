module

public import Lean.Elab.Command
public import Lean.Linter.Basic

open Lean

public section

register_option linter.foo : Bool := {
  defValue := true
  descr := "Whether `fooLinter` is active."
}

open Linter

def fooLinter : Linter where
  run := withSetOptionIn fun cmd => do
    unless getLinterValue linter.foo (← getLinterOptions) do
      return
    unless ← MonadLog.hasErrors do
      return
    logLint linter.foo cmd m!"Hello, world!"

initialize addLinter fooLinter
