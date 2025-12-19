module

import Lean
import Batteries
import all Lean.Parser.Command

/-!
# Naming linter

TODO: docs
-/

open Lean Meta Elab Parser Command

namespace Mathlib.Linter

/-
def declModifiers (inline : Bool) := leading_parser
  optional docComment >>
  optional (Term.«attributes» >> if inline then skip else ppDedent ppLine) >>
  optional visibility >>
  optional «protected» >>
  optional («meta» <|> «noncomputable») >>
  optional «unsafe» >>
  optional («partial» <|> «nonrec»)
-/
/-- Flags and data added to declarations (eg docstrings, attributes, `private`, `unsafe`, `partial`, ...). -/
protected structure Modifiers where
  /-- Input syntax, used for adjusting declaration range (unless missing) -/
  stx             : TSyntax ``Parser.Command.declModifiers
  /--
  The docstring, if present, and whether it's Verso.
  -/
  docString?      : Option (TSyntax ``Parser.Command.docComment)
  attributes?     : Option (TSyntax ``Term.«attributes»)
  visibility?     : Option (TSyntax ``visibility)
  protected?      : Option (TSyntax ``«protected»)
  -- Mutually exclusive with `noncomputable?` (express this?)
  meta?           : Option (TSyntax ``«meta»)
  noncomputable?  : Option (TSyntax ``«noncomputable»)
  unsafe?         : Option (TSyntax ``«unsafe»)
  -- Mutually exclusive with `nonrec?` (express this?)
  partial?        : Option (TSyntax ``«partial»)
  nonrec?         : Option (TSyntax ``«nonrec»)
  deriving Inhabited, Repr

-- instance : ToFormat Modifiers := ⟨fun m =>
--   let components : List Format :=
--     (match m.docString? with
--      | some str => [f!"/--{str}-/"]
--      | none     => [])
--     ++ (match m.visibility with
--      | .regular   => []
--      | .private   => [f!"private"]
--      | .public    => [f!"public"])
--     ++ (if m.isProtected then [f!"protected"] else [])
--     ++ (match m.computeKind with | .regular => [] | .meta => [f!"meta"] | .noncomputable => [f!"noncomputable"])
--     ++ (match m.recKind with | RecKind.partial => [f!"partial"] | RecKind.nonrec => [f!"nonrec"] | _ => [])
--     ++ (if m.isUnsafe then [f!"unsafe"] else [])
--     ++ m.attrs.toList.map (fun attr => format attr)
--   Format.bracket "{" (Format.joinSep components ("," ++ Format.line)) "}"⟩

-- instance : ToString Modifiers := ⟨toString ∘ format⟩

-- /--
-- Retrieve doc string from `stx` of the form `(docComment)?`.
-- -/
-- def expandOptDocComment? [Monad m] [MonadError m] (optDocComment : Syntax) : m (Option String) :=
--   match optDocComment.getOptional? with
--   | none   => return none
--   | some s => match s[1] with
--     | .atom _ val => return some (String.Pos.Raw.extract val 0 (val.rawEndPos.unoffsetBy ⟨2⟩))
--     | _           => throwErrorAt s "unexpected doc string{indentD s[1]}"

section Methods

run_cmd
  let s ← getConstInfo ``Parser.Command.declModifiers
  logInfo m!"{s.value?}"

#check ParserInfo

-- run_cmd do
--   let s := parserExtension.getState (← getEnv)
--   logInfo m!"{s.categories.toArray.map (·.1)}"
--   logInfo m!"{s.tokens.values}"
--   logInfo m!"{s.kinds.toArray.map (·.1)}"

def _root_.Lean.Syntax.getOptionalOfKind? (stx : Syntax) (kind : SyntaxNodeKind) :
    Option (TSyntax kind) := do
  let stx ← stx.getOptional?
  guard <| stx.isOfKind kind
  return ⟨stx⟩

def _root_.Lean.Syntax.mk? (stx : Syntax) {kind : SyntaxNodeKind} : Option (TSyntax kind) :=
  if stx.isOfKind kind then some ⟨stx⟩ else none

/-- Elaborate declaration modifiers (i.e., attributes, `partial`, `private`, `protected`, `unsafe`, `meta`, `noncomputable`, doc string)-/
def mkModifiers (stx : TSyntax ``Parser.Command.declModifiers) : Modifiers where
  stx
  -- We don't use a match because of the `inline` argument to the parser and the awkwardness of dealing with `<|>`.
  docString?     := stx.raw[0].getOptionalOfKind? ``Parser.Command.docComment
  attributes?    := stx.raw[1].getOptionalOfKind? ``Term.«attributes»
  visibility?    := stx.raw[2].getOptionalOfKind? ``visibility
  protected?     := stx.raw[3].getOptionalOfKind? ``«protected»
  -- Mutually exclusive with `noncomputable?` (express this?)
  meta?          := stx.raw[4].getOptionalOfKind? ``«meta»
  noncomputable? := stx.raw[4].getOptionalOfKind? ``«noncomputable»
  unsafe?        := stx.raw[5].getOptionalOfKind? ``«unsafe»
  -- Mutually exclusive with `nonrec?` (express this?)
  partial?       := stx.raw[6].getOptionalOfKind? ``«partial»
  nonrec?        := stx.raw[6].getOptionalOfKind? ``«nonrec»

-- TODO: API relating it to regular `Modifiers` and the tokens used there.

-- TODO: paramterize by kind, possibly; use typed syntax
-- TODO: `declVal` explosion
/-- Like `DefView`, but with finer structure, and without elaboration internals. -/
protected structure DefView where
  kind          : DefKind
  ref           : Syntax
  /--
  An unstructured syntax object that comprises the "header" of the definition, i.e. everything up
  to the value. Used as a more specific ref for header elaboration.
  -/
  headerRef     : Syntax
  modifiers     : Linter.Modifiers
  declId?       : Option Syntax
  -- TODO: make `Array`
  binders       : Syntax
  type?         : Option Syntax
  value?        : Option Syntax
  deriving?     : Option Syntax := none
  deriving Inhabited

-- def DefView.isInstance (view : DefView) : Bool :=
--   view.modifiers.attributes?.any fun attr => attr.name == `instance

open Meta

def mkDefViewOfAbbrev (modifiers : Modifiers) (stx : Syntax) : DefView :=
  -- leading_parser "abbrev " >> declId >> optDeclSig >> declVal
  let (binders, type) := expandOptDeclSig stx[2]
  { ref := stx, headerRef := mkNullNode stx.getArgs[*...3], kind := DefKind.abbrev, modifiers,
    declId? := stx[1], binders, type? := type, value? := stx[3] }

def mkDefViewOfDef (modifiers : Modifiers) (stx : Syntax) : DefView :=
  -- leading_parser "def " >> declId >> optDeclSig >> declVal >> optDefDeriving
  let (binders, type) := expandOptDeclSig stx[2]
  { ref := stx, headerRef := mkNullNode stx.getArgs[*...3], kind := DefKind.def, modifiers,
    declId? := stx[1], binders, type? := type, value? := stx[3], deriving? := stx[4].getOptional? }

def mkDefViewOfTheorem (modifiers : Modifiers) (stx : Syntax) : DefView :=
  -- leading_parser "theorem " >> declId >> declSig >> declVal
  let (binders, type) := expandDeclSig stx[2]
  { ref := stx, headerRef := mkNullNode stx.getArgs[*...3], kind := DefKind.theorem, modifiers,
    declId? := stx[1], binders, type? := some type, value? := stx[3] }

def mkDefViewOfInstance (modifiers : Modifiers) (stx : Syntax) : DefView :=
  -- leading_parser Term.attrKind >> "instance " >> optNamedPrio >> optional declId >> declSig >> declVal
  let (binders, type) := expandDeclSig stx[4]
  {
    ref := stx, headerRef := mkNullNode stx.getArgs[*...5], kind := DefKind.instance, modifiers := modifiers,
    declId? := stx[3].getOptional?, binders := binders, type? := type, value? := stx[5]
  }

def mkDefViewOfOpaque (modifiers : Modifiers) (stx : Syntax) : DefView :=
  -- leading_parser "opaque " >> declId >> declSig >> optional declValSimple
  let (binders, type) := expandDeclSig stx[2]
  {
    ref := stx, headerRef := mkNullNode stx.getArgs[*...3], kind := DefKind.opaque, modifiers := modifiers,
    declId? := stx[1], binders := binders, type? := some type, value? := stx[3].getOptional?
  }

def mkDefViewOfExample (modifiers : Modifiers) (stx : Syntax) : DefView :=
  -- leading_parser "example " >> declSig >> declVal
  let (binders, type) := expandOptDeclSig stx[1]
  { ref := stx, headerRef := mkNullNode stx.getArgs[*...2], kind := DefKind.example, modifiers := modifiers,
    declId? := none, binders := binders, type? := type, value? := stx[2] }

public protected def mkDefView (stx : Syntax) : Option DefView := do
  guard <| isDefLike stx
  let modifiers : TSyntax ``declModifiers ← stx[0].mk?
  let modifiers := mkModifiers modifiers
  let stx := stx[1]
  let declKind := stx.getKind
  -- let modifiers := if modifiers.computeKind == .regular && (← getScope).isMeta &&
  --     declKind != ``Parser.Command.theorem && declKind != ``Parser.Command.example then
  --   { modifiers with computeKind := .meta }
  -- else modifiers
  if declKind == ``Parser.Command.«abbrev» then
    mkDefViewOfAbbrev modifiers stx
  else if declKind == ``Parser.Command.definition then
    mkDefViewOfDef modifiers stx
  else if declKind == ``Parser.Command.theorem then
    mkDefViewOfTheorem modifiers stx
  else if declKind == ``Parser.Command.opaque then
    mkDefViewOfOpaque modifiers stx
  else if declKind == ``Parser.Command.instance then
    mkDefViewOfInstance modifiers stx
  else if declKind == ``Parser.Command.example then
    mkDefViewOfExample modifiers stx
  else
    none


#check Structure.structureSyntaxToView
#check elabInductive
#check elabAxiom
-- Seems that this takes into account Modifiers when turning `declId` into a declName. We could do the same...except that we can't, without "pseudo-elaborating" syntax to take into account all the modifier modifications that have been added thus far by various elaborators. So maybe don't.
#check Elab.expandDeclId
#check expandParents

open Structure

/--
```
def structParent := leading_parser optional (atomic (ident >> " : ")) >> termParser
def «extends»    := leading_parser " extends " >> sepBy1 structParent ", "
```
-/
private def expandParents (optExtendsStx : Syntax) : Array StructParentView :=
  let parentDecls := if optExtendsStx.isNone then #[] else optExtendsStx[0][1].getSepArgs
  parentDecls.map fun parentDecl => Id.run do
    let mut projRef  := parentDecl
    let mut rawName? := none
    let mut name? := none
    unless parentDecl[0].isNone do
      let ident := parentDecl[0][0]
      let rawName := ident.getId
      let name := rawName.eraseMacroScopes
      -- unless name.isAtomic do
      --   throwErrorAt ident "Invalid parent projection name `{name}`: Name must be atomic"
      projRef  := ident
      rawName? := rawName
      name? := name
    let type := parentDecl[1]
    return {
      ref := parentDecl
      projRef
      name?
      rawName?
      type
    }


def DerivingClassView.ofSyntax : TSyntax ``derivingClass → Option DerivingClassView
  | `(Parser.Command.derivingClass| $[@[expose%$expTk?]]? $cls:term) => do
    return { ref := cls, cls, hasExpose := expTk?.isSome }
  | _ => none

def getOptDerivingClasses (optDeriving : Syntax) : Array DerivingClassView :=
  match optDeriving with
  | `(Parser.Command.optDeriving| deriving $[$classes],*) =>
    classes.filterMap DerivingClassView.ofSyntax
  | _ => #[]


/-- View of a constructor. Only `ref`, `modifiers`, `declName`, and `declId` are required by the mutual inductive elaborator itself. -/
structure CtorView where
  /-- Syntax for the whole constructor. -/
  ref       : Syntax
  modifiers : Modifiers -- make syntax?
  -- /-- Fully qualified name of the constructor. -/
  -- declName  : Name
  /-- Syntax for the name of the constructor, used to apply terminfo. If the source is synthetic, terminfo is not applied. -/
  declId    : Syntax
  /-- For handler use. The `inductive` uses it for the binders to the constructor. -/
  binders   : Syntax := .missing
  /-- For handler use. The `inductive` command uses it for the resulting type for the constructor. -/
  type?     : Option Syntax := none

/-- A view for generic inductive types. -/
structure InductiveView where
  ref             : Syntax
  declId          : Syntax
  modifiers       : Modifiers
  class?          : Option (TSyntax ``classTk)
  -- maybe `tk` that is `inductive`, `coinductive`, or `structure`?
  -- /-- Whether the command should allow indices (like `inductive`) or not (like `structure`). -/
  -- allowIndices    : Bool
  -- /-- Whether the command supports creating inductive types that can be polymorphic across both `Prop` and `Type _`.
  -- If false, then either the universe must be `Prop` or it must be of the form `Type _`. -/
  -- allowSortPolymorphism : Bool
  -- shortDeclName   : Name
  -- declName        : Name
  -- levelNames      : List Name
  binders         : Syntax
  type?           : Option Syntax
  ctors           : Array CtorView
  computedFields  : Array ComputedFieldView
  derivingClasses : Array DerivingClassView
  -- /-- The declaration docstring, and whether it's Verso -/
  -- docString?      : Option (TSyntax ``Lean.Parser.Command.docComment × Bool)
  -- isCoinductive : Bool := false
  deriving Inhabited


/--
Represents the data of the syntax of a structure parent.
-/
structure StructParentView where
  ref        : Syntax
  /-- Ref to use for the parent projection. -/
  projRef    : Syntax
  /-- The name of the parent projection (without macro scopes). -/
  name?      : Option Name
  /-- The name of the parent projection (with macro scopes). Used for local name during elaboration. -/
  rawName?   : Option Name
  type       : Syntax

-- inductive StructFieldViewDefault where
--   | optParam (value : Syntax)
--   | autoParam (tactic : Syntax)

/--
Represents the data of the syntax of a structure field declaration.
-/
protected structure StructFieldView where
  ref        : Syntax
  modifiers  : Syntax -- declModifiers; could explode
  binderInfo : BinderInfo
  /-- Ref for the field name -/
  nameId     : Syntax
  /-- The name of the field (without macro scopes). -/
  name       : Name
  /-- The name of the field (with macro scopes).
  Used when adding the field to the local context, for field elaboration. -/
  rawName    : Name
  binders    : Syntax
  type?      : Option Syntax
  default?   : Option StructFieldViewDefault


structure StructView extends InductiveView where
  parents : Array StructParentView
  fields  : Array StructFieldView
  deriving Inhabited

/-
```
def structExplicitBinder := leading_parser atomic (declModifiers true >> "(") >> many1 ident >> optDeclSig >> optional (Term.binderTactic <|> Term.binderDefault) >> ")"
def structImplicitBinder := leading_parser atomic (declModifiers true >> "{") >> many1 ident >> declSig >> "}"
def structInstBinder     := leading_parser atomic (declModifiers true >> "[") >> many1 ident >> declSig >> "]"
def structSimpleBinder   := leading_parser atomic (declModifiers true >> ident) >> optDeclSig >> optional (Term.binderTactic <|> Term.binderDefault)
def structFields         := leading_parser many (structExplicitBinder <|> structImplicitBinder <|> structInstBinder)
```
-/
private def expandFields (structStx : Syntax) : Array Linter.StructFieldView :=
  -- if structStx[4][0].isToken ":=" then
  --   -- https://github.com/leanprover/lean4/issues/5236
  --   let cmd := if structStx[0].getKind == ``Parser.Command.classTk then "class" else "structure"
  --   withRef structStx[0] <| Linter.logLintIf Linter.linter.deprecated structStx[4][0]
  --     s!"`{cmd} ... :=` has been deprecated in favor of `{cmd} ... where`."
  let fieldBinders := if structStx[4].isNone then #[] else structStx[4][2][0].getArgs
  fieldBinders.foldl (init := #[]) fun (views : Array StructFieldView) (fieldBinder : Syntax) => Id.run do
    let mut fieldBinder := fieldBinder
    if fieldBinder.getKind == ``Parser.Command.structSimpleBinder then
      fieldBinder := mkNode ``Parser.Command.structExplicitBinder
        #[ fieldBinder[0], mkAtomFrom fieldBinder "(", mkNullNode #[ fieldBinder[1] ], fieldBinder[2], fieldBinder[3], fieldBinder[4], mkAtomFrom fieldBinder ")" ]
    let k := fieldBinder.getKind
    let binfo :=
      if k == ``Parser.Command.structExplicitBinder then BinderInfo.default
      else if k == ``Parser.Command.structImplicitBinder then BinderInfo.implicit
      else if k == ``Parser.Command.structInstBinder then BinderInfo.instImplicit
      else BinderInfo.default
    let fieldModifiers := fieldBinder[0]
    let (binders, type?, default?) :=
      if binfo == BinderInfo.default then
        let (binders, type?) := expandOptDeclSig fieldBinder[3]
        let optBinderTacticDefault := fieldBinder[4]
        if optBinderTacticDefault.isNone then
          (binders, type?, none)
        else if optBinderTacticDefault[0].getKind != ``Parser.Term.binderTactic then
          -- binderDefault := leading_parser " := " >> termParser
          let value := optBinderTacticDefault[0][1]
          (binders, type?, some <| StructFieldViewDefault.optParam value)
        else
          let binderTactic := optBinderTacticDefault[0]
          let tac := binderTactic[2]
          -- Auto-param applies to `forall $binders*, $type`, which will be handled in `elabFieldTypeValue`
          (binders, type?, some <| StructFieldViewDefault.autoParam tac)
      else
        let (binders, type) := expandDeclSig fieldBinder[3]
        (binders, some type, none)
    let idents := fieldBinder[2].getArgs
    idents.foldl (init := views) fun (views : Array StructFieldView) ident =>
      let rawName := ident.getId
      let name    := rawName.eraseMacroScopes
      return views.push {
        ref        := ident
        modifiers  := fieldModifiers
        binderInfo := binfo
        name
        nameId     := ident
        rawName
        binders
        type?
        default?
      }

/-
leading_parser (structureTk <|> classTk) >> declId >> optDeclSig >> optional «extends» >>
  optional (("where" <|> ":=") >> optional structCtor >> structFields) >> optDeriving

where
def structParent := leading_parser optional (atomic (ident >> " : ")) >> termParser
def «extends» := leading_parser " extends " >> sepBy1 structParent ", " >> optType

def structFields         := leading_parser many (structExplicitBinder <|> structImplicitBinder <|> structInstBinder)
def structCtor           := leading_parser try (declModifiers >> ident >> " :: ")
-/
def structureSyntaxToView (modifiers : Modifiers) (stx : Syntax) : Option StructView := do
  let isClass   := stx[0].getKind == ``Parser.Command.classTk
  let declId    := stx[1]
  let (binders, type?) := expandOptDeclSig stx[2]
  let exts := stx[3]
  let type? :=
    -- Compatibility mode for `structure S extends P : Type` syntax
    if type?.isNone && !exts.isNone && !exts[0][2].isNone then
      -- logWarningAt exts[0][2][0] <| "\
      --   The syntax is now `structure S : Type extends P` rather than `structure S extends P : Type`"
      --   ++ .note "The purpose of this change is to accommodate `structure S extends toP : P` syntax for naming parent projections."
      some exts[0][2][0][1]
    else
      -- if !exts.isNone && !exts[0][2].isNone then
      --   logErrorAt exts[0][2][0] <| "\
      --       Unexpected additional resulting type. \
      --       The syntax is now `structure S : Type extends P` rather than `structure S extends P : Type`."
      --       ++ .note "The purpose of this change is to accommodate `structure S extends toP : P` syntax for naming parent projections."
      type?
  let parents := expandParents exts
  let derivingClasses := getOptDerivingClasses stx[5]
  let fields := expandFields stx -- from declId...seems resolved though
  -- Private fields imply a private constructor (in the module system only, for back-compat)
  let ctor := expandCtor
    (forcePrivate := (← getEnv).header.isModule && fields.any (·.modifiers.isPrivate))
    stx modifiers declName
  fields.forM fun field => do
    if field.declName == ctor.declName then
      throwErrorAt field.ref "Invalid field name `{field.name}`: This is the name of the structure constructor"
    addDeclarationRangesFromSyntax field.declName field.ref
  return {
    ref := stx
    declId
    modifiers
    isClass
    shortDeclName := name
    declName
    levelNames
    binders
    type?
    allowIndices := false
    allowSortPolymorphism := false
    ctors := #[ctor]
    parents
    fields
    computedFields := #[]
    derivingClasses
    docString?
  }
/-
```
@[builtin_command_parser] def declaration := leading_parser
  declModifiers false >>
  («abbrev» <|> definition <|> «theorem» <|> «opaque» <|> «instance» <|> «axiom» <|> «example» <|>
   «inductive» <|> «coinductive» <|> classInductive <|> «structure»)
```
-/
def Lean.Syntax.getDeclId (stx : TSyntax ``declaration) : Option (TSyntax ``declId) :=
  Linter.mkDefView stx |>.bind (·.declId?)
