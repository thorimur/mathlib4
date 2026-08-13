module

-- public import Lean
-- public import Qq
import all Mathlib.Cafe.Module.Meta.Z
import Lean

import Lean.Elab.Command

public meta def bar (n : Std.Queue Bool) : Std.Queue Bool := .enqueue true n

open Lean


run_cmd
  let some a := Lean.IR.findEnvDecl (← getEnv) <|
    mkPrivateNameCore (`Mathlib.Cafe.Module.Meta.Z) `tPrivateMetaDef!
    | throwError "Couldn't find it!"
  logInfo m!"{a}"

run_cmd
  let some a := Lean.IR.findEnvDecl (← getEnv) <|
    mkPrivateNameCore (`Mathlib.Cafe.Module.Meta.Y) `s
    | throwError "Couldn't find s!"
  logInfo m!"{a}"

#eval tPrivateMetaDef! 4

-- run_cmd
--   -- logInfo m!"{isMarkedMeta (← getEnv) ``Nat.beq}"
--   -- logInfo m!"{isDeclMeta (← getEnv) ``bar}"
--   logInfo m!"{repr <| getIRPhases (← getEnv) ``Std.Queue.enqueue}"

#exit
open Qq Lean

syntax "foo" num : term

set_option trace.Compiler true

meta def baz : Nat := 4

public structure Foo where
  x : Nat



theorem bar_eq : bar 4 = true := rfl

public meta def b := Lean.Expr.const `foooefefw []

set_option pp.qq false

#print b

@[noinline]
public meta def bar' (n : Nat) : BaseIO Unit := return

public meta def bar₁ : BaseIO Unit := do bar' 3; bar' 4

elab_rules : term
| `(foo $n:num) =>
  return if barRegular n.getNat then Expr.const ``Bool.true [] else Expr.const ``Bool.false []
