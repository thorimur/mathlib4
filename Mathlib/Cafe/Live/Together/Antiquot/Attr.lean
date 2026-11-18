module

public import Lean

open Lean Parser

public section

namespace Mathlib.Parser

initialize combinatorMatchAttribute : ParserCompiler.CombinatorAttribute ←
  ParserCompiler.registerCombinatorAttribute
    `combinator_match
    "Register a match case generator for a parser combinator"


structure CaseSyntax where
  kind : SyntaxNodeKind
  antiquot? : Option Syntax
  children : Array CaseSyntax

inductive SyntaxCases.Context where
| top
| inner
| inAntiquot

def SyntaxCases.Context.down : Context → Context
| .top => .inner
| ctx => ctx

abbrev SyntaxCases := SyntaxCases.Context → Array (Array Syntax)

/-
- Given parser, get its cases one level down, as though it's an inductive type

no


-/

unsafe initialize matchGenAttribute : KeyedDeclsAttribute SyntaxCases ←
  KeyedDeclsAttribute.init {
    name := `match_generator,
    descr := "Register a match case generator for a parser.",
    valueTypeName := ``Mathlib.Parser.SyntaxCases,
    evalKey := fun builtin stx => do
      let env ← getEnv
      let stx ← Attribute.Builtin.getIdent stx
      let id := stx.getId
      -- `isValidSyntaxNodeKind` is updated only in the next stage for new `[builtin*Parser]`s, but we try to
      -- synthesize a formatter for it immediately, so we just check for a declaration in this case
      unless (builtin && (env.find? id).isSome) || Parser.isValidSyntaxNodeKind env id do
        throwError "Invalid `[formatter]` argument: Unknown syntax kind `{id}`"
      if (← getEnv).contains id then
        recordExtraModUseFromDecl (isMeta := false) id
        if (← Elab.getInfoState).enabled then
          Elab.addConstInfo stx id none
      pure id
  }

unsafe initialize ParserCompiler.registerParserCompiler {
  varName := `matchGen
  categoryAttr := matchGenAttribute
  combinatorAttr := combinatorMatchAttribute
}
