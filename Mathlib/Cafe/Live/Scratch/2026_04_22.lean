import Qq
open Qq Lean

set_option backward.do.legacy false

#check Bind.bind


set_option trace.compiler.ir.result true in
def foo₂ : MetaM Bool := do
  letI f (a : Array Nat) : Bool := a.size = 2
  return f #[1,2] && f #[7]

#print foo₂
set_option pp.explicit true
#print foo₂

#eval foo₂ q(Nat)  -- false
#eval foo₂ q(Int)  -- false

#show_stx!
public def foo := true

#check Lean.ConstantInfo

open Lean Elab Meta Command Tactic



def xd : CommandElabM Unit := do
  let env ← getEnv
  let some x := env.find? ``foo
    | throwError "Couldn't find foo!"
  logInfo m!"Got {x.type} @ {← getRef}"

#print xd

#check TacticM
/-
String

Syntax

CommandElabM, TacticM



-/
set_option pp.rawOnError true

#check Info.ofCompletionInfo

def x : Option Bool :=
  let d := 4; some true

#check Expr

elab "#foo" : command => do
  let env ← getEnv
  let d ← liftCoreM <| isInstance ``foo
  let some x := env.find? ``foo
    | throwError "Couldn't find foo!"
  logInfo m!"Got {x.type} @ {← getRef}"

open Qq

def bar : MetaM Bool := do
  let x := q()

def baz : TermElabM Bool := do
  let x ← bar
  return !x

#foo

namespace Foo

#check Lean.Elab.Command.elabDeclaration
