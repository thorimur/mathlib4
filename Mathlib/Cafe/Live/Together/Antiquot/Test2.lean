import Mathlib.Cafe.Live.Together.Antiquot.CaseGenerator

open Lean Mathlib Parser

public meta section

@[command_parser]
def verySimpleStx : Parser := node decl_name% "#very_simple"

@[command_parser]
def lessSimpleStx : Parser := node decl_name% (verySimpleStx >> verySimpleStx)

@[command_parser]
def simpleStx : Parser := leading_parser "#simple_stx" >> ppSpace >> ((nonReservedSymbol "term" >> ppSpace >> termParser) <|> (nonReservedSymbol "command" >> ppSpace >> commandParser))

syntax commandArg := &"command " command

syntax "#nice_stx " ((&"term " term) <|> commandArg <|> ident) : command

@[run_parser_attribute_hooks]
def _root_.ident.antiquot := Lean.Parser.ident



/--
info: `failed to pretty print term (use 'set_option pp.rawOnError true' for raw representation)`
(«command#nice_stxTerm___»
 "#nice_stx"
 (group
  "term"
  (ident.antiquot
   "$"
   []
   `x._@.Mathlib.Cafe.Live.Together.Antiquot.Test2.524820659._hygCtx._hyg.2
   (antiquotName ":" "ident"))))
-/
#guard_msgs in
run_cmd
  let x ← `(command|#nice_stx term $$x:ident)
  logInfo m!"`{x}`\n{format x}"
set_option pp.rawOnError true
#show_match_cases verySimpleStx
/--
info: values: [[[#simple_stx term $x:term],
  [[Error pretty printing syntax: Unknown constant `command.pseudo.antiquot`. Falling back to raw printer.]
   (simpleStx "#simple_stx" "command" (command.pseudo.antiquot "$" [] `x (antiquotName ":" "command")))]]]
-/
#guard_msgs in
#show_match_cases pp simpleStx
