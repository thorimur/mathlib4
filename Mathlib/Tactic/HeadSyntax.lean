module

public meta import Lean

open Lean Elab Term Command

public meta section

syntax elabArgsSpec := num noWs (("..." noWs num) <|> "...*")?

syntax (name := headSyntax)
  (Parser.Command.docComment)? (Parser.Term.«attributes»)? Parser.Term.attrKind
  "head_syntax "
  Parser.Command.optNamedName Parser.Command.optNamedPrio
  ("(" &"elabArgs" " := " elabArgsSpec ") ")?
  (ppSpace stx:arg)+ : command

structure HeadSyntaxResult where
  headAbbrev : Name
  noArgsKind : Name
  argsKind : Name
deriving Repr, Inhabited

/-- Gets the presolved name produced by `mkCIdent`, or else `.anonymous`. -/
def _root_.Lean.Syntax.getCIdent : Syntax → Name
  | .ident (preresolved := [.decl c []]) .. => c
  | _ => .anonymous

/-- Gets the presolved name produced by `mkCIdent`, or else `.anonymous`. -/
@[inline] def _root_.Lean.Syntax.Ident.getCIdent (id : Ident) := id.raw.getCIdent

/-- Gets the presolved name produced by `mkCIdent`, or else `.anonymous`. -/
@[inline] def _root_.Lean.TSyntax.getCIdent (id : TSyntax `ident) := id.raw.getCIdent

/- both of these are macros on argsKind. if `tooMany > 1`, add the first.
If `tooMany = 1`, the second. -/

/-- Assumes `tooMany > 1` (i.e. at least one argument). This is only applied to the `argsKind` node,
so we assume a certain structure. -/
@[inline] def expandOverAppArgs (tooMany : Nat) : Macro :=
  -- Structure: `argsKind[headAbbrev[...], null[...:term*]]`
  fun stx => do
    let #[_headAbbrevNode, argsNode] := stx.getArgs | Macro.throwUnsupported
    let args := argsNode.getArgs
    if args.size < tooMany then return stx else
      let overAppArgs := args.extract tooMany args.size
      -- Try to modify `stx` in place at the `null` node
      let stx := stx.modifyArg 1 (·.modifyArgs (·.shrink tooMany))
      return mkNode `Lean.Parser.Term.app #[stx, mkNullNode overAppArgs]

/-- The `tooMany = 1` case. -/
@[inline] def expandOverAppNoArgs (noArgsKind : Name) : Macro :=
  -- Structure: `argsKind[headAbbrev[...], null[...:term*]]`
  -- Transform to `app[noArgsKind[headAbbrev[...]], null[...*term]`
  fun stx => do
    let #[headAbbrevNode, argsNode] := stx.getArgs | Macro.throwUnsupported
    let head := mkNode noArgsKind #[headAbbrevNode]
    return mkNode `Lean.Parser.Term.app #[head, argsNode]

/- if `lower > 0`, add both of these `TermElab`s to `argsKind` and `noArgsKind`. -/

open Term in
/-- Errors if `argsKind` has less then `lower` arguments. -/
def checkLowerBoundArgs (lower : Nat) : TermElab := fun stx _ => do
  -- Structure: `argsKind[headAbbrev[...], null[...:term*]]`
  let #[headAbbrevNode, argsNode] := stx.getArgs | throwUnsupportedSyntax
  let numArgs := argsNode.getArgs.size
  if numArgs < lower then
    -- TODO: bad idea? on second thought kind of makes it deceptively like a parser error
    let pos := stx.getTailPos?.map (fun pos => Syntax.ofRange ⟨pos, pos⟩)
    withRef? pos do
      throwError "Expected at least {lower} argument{if lower = 1 then "" else "s"} \
        to `{headAbbrevNode}`, found only {numArgs}"
  else throwUnsupportedSyntax -- fall back to other elab rules

open Term in
/-- Errors on `noArgsKind` and reports that it ought to have at least `lower` arguments. -/
def checkLowerBoundNoArgs (lower : Nat) : TermElab := fun stx _ => do
  let pos := stx.getTailPos?.map (fun pos => Syntax.ofRange ⟨pos, pos⟩)
  withRef? pos do
    throwError "Expected at least {lower} argument{if lower = 1 then "" else "s"} \
      to `{stx}`, found none"

open Command
def getElabArgsRange : TSyntax ``elabArgsSpec → CommandElabM (Nat × Option Nat)
  | `(elabArgsSpec| $n:num) => do
    let n := n.getNat
    return (n, some <| n + 1)
  | `(elabArgsSpec| $n...$k:num) => do
    let nNat := n.getNat; let kNat := k.getNat
    unless nNat < kNat do
      throwErrorAt k m!"The (exclusive) upper bound on elaboration arguments `{k}` must be \
        greater than the (inclusive) lower bound `{n}`."
    return (nNat, kNat)
  | `(elabArgsSpec| $n...*) =>
    return (n.getNat, none)
  | _ => throwUnsupportedSyntax

/-- Assumes the identifiers have been produced by `mkCIdent`. -/
elab (name := _applyNatInternal) &"_apply_nat% " c:ident n:num : term =>
  return .app (mkConst c.getCIdent) (toExpr n.getNat)

/-- Assumes the identifiers have been produced by `mkCIdent`. -/
elab (name := _applyIdentInternal) &"_apply_ident% " c:ident id:ident : term =>
  return .app (mkConst c.getCIdent) (toExpr id.getCIdent)

def mkApplyNatInternal (c : Name) (n : Nat) : TSyntax ``_applyNatInternal :=
  mkNode ``_applyNatInternal #[
    mkAtom "_apply_nat%",
    mkCIdent c,
    Syntax.mkNatLit n]

def mkApplyIdentInternal (c id : Name) : TSyntax ``_applyIdentInternal :=
  mkNode ``_applyIdentInternal #[
    mkAtom "_apply_nat%",
    mkCIdent c,
    mkCIdent id]


/-
def optKind : Parser := optional (" (" >> nonReservedSymbol "kind" >> ":=" >> ident >> ")")
@[builtin_command_parser] def «macro_rules» := suppressInsideQuot <| leading_parser
  optional docComment >> optional Term.«attributes» >> Term.attrKind >>
  "macro_rules" >> optKind >> Term.matchAlts
@[builtin_command_parser] def «syntax»      := leading_parser
  optional docComment >> optional Term.«attributes» >> Term.attrKind >>
  "syntax " >> optPrecedence >> optNamedName >> optNamedPrio >> many1 (ppSpace >> syntaxParser argPrec) >> " : " >> ident
@[builtin_command_parser] def syntaxAbbrev  := leading_parser
  optional docComment >> optional visibility >> "syntax " >> ident >> " := " >> many1 syntaxParser
-/

--

open Elab Term Command in
def elabHeadSyntax : Syntax → CommandElabM HeadSyntaxResult
  | `(headSyntax| $[$doc:docComment]? $[@[$attrs,*]]? $attrKind:attrKind
      head_syntax%$tk $[(name := $id)]? $[$prio:namedPrio]? $[(elabArgs := $args?)]?
        $[$stx:stx]*) => do
    let some id := id | throwErrorAt tk "`head_syntax` must be followed by `(name := ...)`."
    let headName := id.getId ++ `head
    let vis := Parser.Command.visibility.ofAttrKind attrKind
    -- return default
    elabSyntaxAbbrev <|← `($[$doc]? $vis syntax%$tk $(mkIdentFrom id headName) := $[$stx:stx]*)
    -- Unfortunately `elabSyntaxAbbrev` does not return this,
    -- but the logic is simple enough to inline.
    let headAbbrevFullName := (← getCurrNamespace) ++ headName
    let headAbbrev := mkCIdentFrom id headAbbrevFullName
    let noArgsKind ← elabSyntax <|← `(command|
      $[$doc]? $[@[$attrs,*]]?
      $attrKind syntax%$tk (name := $(mkIdentFrom id <| id.getId ++ `noArgs)) $[$prio]?
        $headAbbrev:ident : term)
    let argsKind ← elabSyntax <|← `(command|
      $[$doc]? $[@[$attrs,*]]?
      $attrKind syntax%$tk:lead%$tk (name := $(mkIdentFrom id <| id.getId ++ `args)) $[$prio]?
        $headAbbrev:ident (ppSpace colGt term:arg)+ : term)
    if let some args := args? then
      let (lower, tooMany?) ← getElabArgsRange args
      let appendAttr (attr) :=
        match attrs with
        | some attrs => attrs.getElems.push attr
        | none => #[attr]
      if let some tooMany := tooMany? then
        let macroAttrs := appendAttr <|← `(Parser.Term.attrInstance|
          $attrKind:attrKind macro $(mkIdentFrom id argsKind))
        -- TODO: I wish antiquotations recognized that this was a term...
        let body : Term :=
          if tooMany > 1 then ⟨mkApplyNatInternal ``expandOverAppArgs tooMany⟩
          else ⟨mkApplyIdentInternal ``expandOverAppNoArgs noArgsKind⟩
        elabCommand <|← `($[$doc:docComment]? @[$macroAttrs,*] $vis:visibility
          aux_def $(mkIdentFrom tk argsKind (canonical := true)) expandOverApp : Macro := $body)
      if lower > 0 then
        let elabNoArgsAttrs := appendAttr <|← `(Parser.Term.attrInstance|
          $attrKind:attrKind term_elab $(mkIdentFrom id noArgsKind))
        let body : Term := ⟨mkApplyNatInternal ``checkLowerBoundNoArgs lower⟩
        elabCommand <|← `($[$doc:docComment]? @[$elabNoArgsAttrs,*] $vis:visibility
          aux_def $(mkIdentFrom tk noArgsKind (canonical := true)) checkLowerNoArgs : TermElab :=
            $body)
        if lower > 1 then
          let elabArgsAttrs := appendAttr <|← `(Parser.Term.attrInstance|
            $attrKind:attrKind term_elab $(mkIdentFrom id argsKind))
          let body : Term := ⟨mkApplyNatInternal ``checkLowerBoundArgs lower⟩
          elabCommand <|← `($[$doc:docComment]? @[$elabArgsAttrs,*] $vis:visibility
            aux_def $(mkIdentFrom tk argsKind (canonical := true)) checkLowerArgs : TermElab :=
              $body)
    return { headAbbrev := headAbbrevFullName, noArgsKind, argsKind }
  | _ => throwUnsupportedSyntax

@[command_elab headSyntax] def elabHeadSyntaxCmd : CommandElab := fun cmd => do
  discard <| elabHeadSyntax cmd

-- head_syntax (name := tPercent') (elabArgs := 1...*) "T%'"

syntax termArg := ident

/-
Should be able to write something like
```
app_elab <head syntax declaration> on t₁ t₂ ts* => do ...
```


-/

syntax termArgs := "noArgs" <|> (termArg* (termArg noWs "*")?)

def termArgToIdent! : TSyntax ``termArg → Ident
  | `(termArg| $i:ident) => i
  | _ => default

open Elab Command
def termArgsToElabRange : TSyntax ``termArgs →
      -- the ident and it's type? Still not sure how we're going to extract from the array/match...
      CommandElabM (Array (Term × Term) × TSyntax ``elabArgsSpec)
  | `(termArgs| noArgs) => return (#[], ← `(elabArgsSpec| 0))
  | `(termArgs| $singleTerms:termArg* $[$rest*]?) =>

  | _ => default

syntax (name := headElab)
  (Parser.Command.docComment)? (Parser.Term.«attributes»)? Parser.Term.attrKind
  "app_elab "
  Parser.Command.optNamedName Parser.Command.optNamedPrio
  (ppSpace Parser.Command.macroArg)+ " on " termArgs " => " term : command



open Elab Term Command in
def elabHeadElab : Syntax → CommandElabM HeadSyntaxResult
  | `(headElab| $[$doc:docComment]? $[@[$attrs,*]]? $attrKind:attrKind
      app_elab%$tk $[(name := $id)]? $[$prio:namedPrio]?
        $[$elabStx]* on $ts:termArgs => $body:term) => do
    let (stxParts, patArgs) := (← elabStx.mapM expandMacroArg).unzip
    -- need to match this against [0] after elabHeadSyntaxing
