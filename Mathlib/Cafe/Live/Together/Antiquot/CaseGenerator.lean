module

public import Mathlib.Cafe.Live.Together.Antiquot.Attr
import Mathlib.Cafe.Live.Together.Antiquot.ShowCases
import all Lean.Parser.Basic
import all Lean.Parser.Types
import all Lean.Parser.Extra
import all Lean.Parser.Do
import all Lean.Parser.Term
import all Lean.Parser.Command
import all Lean.Parser.Syntax
import all Lean.Parser.Term.Basic
import Batteries

open Lean Mathlib Parser

namespace Mathlib.Parser

public section




#print leadingNode
-- #print verySimpleStx

#check withCache

@[combinator_match withFn, expose]
def withFn.matchGen (_ : ParserFn → ParserFn) (p : SyntaxCases) : SyntaxCases := p

attribute [run_parser_attribute_hooks] withCache

@[combinator_match withAntiquot, expose]
def withAntiquot.matchGen (antiquotP p : SyntaxCases) : SyntaxCases
  | .top => p .inner
  | _ => antiquotP .inAntiquot

@[combinator_match checkPrec, expose]
def checkPrec.matchGen (_prec : Nat) : SyntaxCases
  | _ => #[#[]]

@[combinator_match checkLhsPrec, expose]
def checkLhsPrec.matchGen (_prec : Nat) : SyntaxCases
  | _ => #[#[]]

@[combinator_match setLhsPrec, expose]
def setLhsPrec.matchGen (_prec : Nat) : SyntaxCases
  | _ => #[#[]]

@[combinator_match checkNoWsBefore, expose]
def checkNoWsBefore.matchGen (_err : String) : SyntaxCases
  | _ => #[#[]]

@[combinator_match checkColEq, expose]
def checkColEq.matchGen (_err : String) : SyntaxCases
  | _ => #[#[]]

@[combinator_match checkLineEq, expose]
def checkLineEq.matchGen (_err : String) : SyntaxCases
  | _ => #[#[]]

@[combinator_match checkColGe, expose]
def checkColGe.matchGen (_err : String) : SyntaxCases
  | _ => #[#[]]

@[combinator_match checkColGt, expose]
def checkColGt.matchGen (_err : String) : SyntaxCases
  | _ => #[#[]]

@[combinator_match checkNoImmediateColon, expose]
def checkNoImmediateColon.matchGen : SyntaxCases
  | _ => #[#[]]

@[combinator_match skip, expose]
def skip.matchGen : SyntaxCases
  | _ => #[#[]]

@[combinator_match _root_.ite, expose, macro_inline]
def ite {_ : Type} (c : Prop) [Decidable c] (t e : SyntaxCases) : SyntaxCases :=
  if c then t else e

@[combinator_match pushNone, expose]
def pushNone.matchGen : SyntaxCases
  | _ => #[#[mkNullNode]]

@[combinator_match manyNoAntiquot, expose]
def manyNoAntiquot.matchGen (_p : SyntaxCases) : SyntaxCases
  | _ => #[#[mkNullNode]]

@[combinator_match antiquotExpr, expose]
def antiquotExpr.matchGen : SyntaxCases
  | _ => #[#[mkIdent `x]] -- generic name replaced later by "frontend"

-- TODO: anonymous antiquotation instead of splitting children all the time?
@[combinator_match orelse, expose]
def orelse.matchGen (p q : SyntaxCases) : SyntaxCases
  | .inAntiquot => p .inAntiquot -- CURSED!
  | lvl => p lvl.down ++ q lvl.down

-- TODO: how do we handle "blocking" nonreservedsymbols which mean that we should *not* continue casing?

/-
@[builtin_doc] def mkAntiquot (name : String) (kind : SyntaxNodeKind) (anonymous := true) (isPseudoKind := false) : Parser :=
  let kind := kind ++ (if isPseudoKind then `pseudo else .anonymous) ++ `antiquot
  let nameP := node `antiquotName <| checkNoWsBefore ("no space before ':" ++ name ++ "'") >> symbol ":" >> nonReservedSymbol name
  -- if parsing the kind fails and `anonymous` is true, check that we're not ignoring a different
  -- antiquotation kind via `noImmediateColon`
  let nameP := if anonymous then nameP <|> checkNoImmediateColon >> pushNone else nameP
  -- antiquotations are not part of the "standard" syntax, so hide "expected '$'" on error
  leadingNode kind maxPrec <| atomic <|
    setExpected [] "$" >>
    manyNoAntiquot (checkNoWsBefore "" >> "$") >>
    checkNoWsBefore "no space before spliced term" >> antiquotExpr >>
    nameP
-/
-- @[combinator_match mkAntiquot, expose]
-- def mkAntiquot.matchGen (name : String) (kind : SyntaxNodeKind) (anonymous : Bool)
--     (isPseudoKind : Bool) : SyntaxCases
--   | _ =>
--     let kind := kind ++ (if isPseudoKind then `pseudo else .anonymous) ++ `antiquot


@[combinator_match symbol, expose]
def symbol.matchGen (sym : String) : SyntaxCases
  | _ => #[#[mkAtom .none sym]] -- TODO: `%$tk` outside of `.inAntiquot` case

@[combinator_match nonReservedSymbol, expose]
def nonReservedSymbol.matchGen (sym : String) : SyntaxCases
  | _ => #[#[mkAtom .none sym]] -- TODO: `%$tk` outside of `.inAntiquot` case; also, this isn't true

@[combinator_match node, expose]
def node.matchGen (kind : SyntaxNodeKind) (p : SyntaxCases) : SyntaxCases
  | lvl => p lvl.down |>.map fun stack => #[.node .none kind stack]

@[combinator_match andthen, expose]
def andthen.matchGen (p q : SyntaxCases) : SyntaxCases
  | lvl =>
    let pstacks := p lvl.down
    let qstacks := q lvl.down
    pstacks.flatMap fun stack => qstacks.map (stack ++ ·)

attribute [run_parser_attribute_hooks] leadingNode mkAntiquot ppSpace ppLine

#print mkAntiquot.matchGen

@[combinator_match categoryParser, expose]
def categoryParser.matchGen (kind : Name) (_rbp : Nat) : SyntaxCases :=
  mkAntiquot.matchGen kind.toString kind true true

@[combinator_match ident, expose]
def ident.matchGen : SyntaxCases :=
  mkAntiquot.matchGen "ident" identKind

@[combinator_match numLit, expose]
def numLit.matchGen : SyntaxCases :=
  mkAntiquot.matchGen "num" numLitKind

@[combinator_match strLit, expose]
def strLit.matchGen : SyntaxCases :=
  mkAntiquot.matchGen "str" strLitKind

@[combinator_match charLit, expose]
def charLit.matchGen : SyntaxCases :=
  mkAntiquot.matchGen "char" charLitKind

@[combinator_match nameLit, expose]
def nameLit.matchGen : SyntaxCases :=
  mkAntiquot.matchGen "name" nameLitKind

@[combinator_match scientificLit, expose]
def scientificLit.matchGen : SyntaxCases :=
  mkAntiquot.matchGen "scientific" scientificLitKind

@[combinator_match hexnum, expose]
def hexnum.matchGen : SyntaxCases :=
  mkAntiquot.matchGen "hexnum" hexnumKind

@[combinator_match hygieneInfo, expose]
def hygieneInfo.matchGen : SyntaxCases :=
  mkAntiquot.matchGen "hygieneInfo" hygieneInfoKind false

-- New declaration for each (sequence of) orelse?
--
-- Check if antiquotatable nodekind we're splitting apart, else anon?
-- Check if all disjuncts have antiquotations, else force anonymous
-- antiquotations propagate!
-- also: (("tk " str) <|> num)
-- also: (("tk " str) <|> num)
-- matches everything, says `str`:
-- syntax (name := test₁) "#fooo₁" (atomic(num hygieneInfo num) <|> str)? : command

syntax (name := test₁) "#fooo₁" (atomic(num hygieneInfo) <|> num)? : command

syntax (name := test₂) "#fooo₂" (num)? : command

syntax (name := test₃) "#fooo₃" (atomic("tk" num) <|> ("tk" str))* : command

#show_stx #fooo₁ $[$x]?
#show_stx #fooo₁ $[$x:num]?

#info_trees in
def teeest₃ : Syntax → Bool
  | `(test₃|#fooo₃ $[tk $x]*) => true -- infotrees lie on original hover!
  -- | `(test₃|#fooo₃ $[$x:num]?) => true
  -- | `(token.tk| tk) => none
  | _ => false

def teeest : Syntax → Bool
  | `(test₁|#fooo₁ $[$x:num $_:hygieneInfo]?) => true
  | `(test₁|#fooo₁ $[$x:num]?) => true
  -- | `(token.tk| tk) => none
  | _ => false
/--
info: def Mathlib.Parser.teeest : Syntax → Bool :=
fun x ↦
  have __discr := x;
  if __discr.isOfKind `Mathlib.Parser.test₁ = true then
    have __discr_1 := __discr.getArg 0;
    have __discr_2 := __discr.getArg 1;
    have yes := fun x x_1 ↦ true;
    if __discr_2.isNone = true then yes () none
    else
      have __discr_3 := __discr_2;
      if __discr_3.matchesNull 1 = true then
        have __discr_4 := __discr_3.getArg 0;
        if __discr_4.isOfKind `group = true then
          have __discr_5 := __discr_4.getArg 0;
          have __discr_6 := __discr_4.getArg 1;
          if __discr_6.isOfKind `hygieneInfo = true then
            have __discr_7 := __discr_6.getArg 0;
            if __discr_7.matchesIdent Name.anonymous = true then
              have x := { raw := __discr_5 };
              yes () (some x)
            else
              have __discr_8 := __discr_6.getArg 0;
              have __discr := __discr.getArg 1;
              false
          else
            have __discr_7 := __discr_4.getArg 1;
            have __discr := __discr.getArg 1;
            false
        else
          have __discr_5 := __discr_3.getArg 0;
          have __discr := __discr.getArg 1;
          false
      else
        have __discr_4 := __discr_2;
        have __discr := __discr.getArg 1;
        false
  else
    have __discr := x;
    false
-/
#guard_msgs in
#print teeest
set_option pp.rawOnError true
run_cmd
  let e ← `(command| #fooo₃ tk "a")
  logInfo m!"{teeest₃ e}"
#check mkAntiquotSplice

attribute [run_parser_attribute_hooks] termParser commandParser doElemParser syntaxParser
  tacticParser

attribute [run_parser_attribute_hooks] Parser.Command.declaration

set_option pp.notation false
#print leadingNode
#print leadingNode.matchGen
