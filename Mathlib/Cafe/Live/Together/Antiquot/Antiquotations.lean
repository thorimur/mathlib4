module

public import Lean
import Mathlib.Util.WhatsNew

open Lean

#check TSyntax

#check Parser.Command.check

public section

-- set_option trace.Elab.step true
set_option pp.rawOnError true
def foo : Syntax → Bool
  | `(command| #check $__:ident) => true
  | _ => by_elab logInfo m!"hit"; return (Expr.const ``Bool.false [])

#check Syntax.node
#check Syntax.ident

namespace Foo

syntax new := "#foo" (num <|> str)

syntax "#look" new : term

#print Foo.new

end Foo

open Parser

#whats_new in
def Foo.manualParser : Parser := leading_parser "#foo_manual"

#print Foo.manualParser

#whats_new in
syntax (name := whateverCmd) "#whatever" : command

syntax (name := noAntiCmd) "#no_antiquot" : command


$$$$$$$$$$$$$$$$$$$$$x:classTk myClass where
  foo : Nat := by grind

#print myClass

run_cmd
  logInfo m!"{isClass (← getEnv) ``myClass}"
-- def foo : Syntax → Bool
--   | `(command| $x:whateverCmd) => true
--   | _ => by_elab logInfo m!"hit"; return (Expr.const ``Bool.false [])

meta def myParser : Parser := node `foo termParser

/-
- Want:

-/

syntax (name := test) "#look_at " myParser : command

#print myParser.formatter

#check ParserDescr

run_cmd
  let tk : Syntax ← `(1)
  let new ← `(term|$$new:new%$tk)
  logInfo m!"{format new}"

elab "#show_stx" t:term : command => logInfo m!"{format t}"

#check Parser.mkAntiquot

#show_stx #look $new:new%$tk

example : Syntax → Bool
  | `(Foo.new| $foo:new) => true
  | _ => false

example : Syntax → Bool
  | `(Foo.new| #foo $s:str) => true
  | `(Foo.new| #foo $n:num) => true
  | _ => false



#check $foo

#print foo
