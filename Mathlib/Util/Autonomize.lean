module

public import Lean
public meta import Lean.Elab.BuiltinCommand
public meta import Lean.PrettyPrinter.Delaborator
import Batteries

-- set_option pp.explicit true

-- run_cmd do
--   let opts ← Lean.getOptions
--   Lean.logInfo m!"{(← Lean.Elab.Command.getScopes).length}"

#check Add

def Add'.{u} (α : Type u) : Type u := sorry



public meta section




/-!
# `#autonomize` for isolating declarations from their scopes

`#autonomize` suggests a modification to the following declaration syntax that isolates it from the surrounding scopes.

## Implementation details

We need to include the following:

```
autonomous

(@[$attrs*])? (public)? (meta)? (noncomputable)? section -- only if any isSome
(universe ...)?

-- Interleaved:
(namespace $currNamespace)? -- invariant: only a single component added at a time
(open ...)?
(open scoped )?
-- end interleaved
(set_option ... in)?
(variable ... in)? -- Note that while we *should* have to be careful about where variables are elaborated wrt namespaces and opens, lean actually does not care. This is a bug.
cmd -- replace decl with `_root_`.
-- end namespaces

(end)? -- if sections exist
```

I'm wondering if we need to decouple the API for `Scope`s in the state from the API for environment extension scopes. I mean, can we literally just store the whole stack and reset the state, instead of worrying about pushScope and popScope?

TODO: notation and syntax that's used, dependencies in the current file, dependencies on environment extension states...and finally, imports
-/



open Lean Elab Command

section defLike

open Lean

syntax defLike := "def_like " term
syntax theoremLike := "theorem_like " term
-- syntax instanceLike := "instance_like " ident
syntax (name := declarationLike) Parser.Command.declModifiersF
  (defLike <|> theoremLike) : command

-- def suggestDeclWithType (n : Name) : CommandElabM Name := do
open Lean Meta Elab Parser PrettyPrinter Delaborator SubExpr Command

local instance : Repr Std.Format.FlattenBehavior := ⟨fun _ _ => f!"<flatten>"⟩

deriving instance Repr for Std.Format

instance : Repr Options where
  reprPrec opts _ := Id.run do
    let mut f := #[]
    for (n, v) in opts do
      unless f.isEmpty do f := f.push f!", "
      f := f.push f!"({n}, {v})"
    return .bracket "{ " (f.foldl (init := .nil) (· ++ ·)) " }"

deriving instance Repr for OpenDecl, Scope

/- autocomplete for end? based on variable names would be cool. -/

elab "#scopes" : command => do
  logInfo m!"{repr <|← getScopes}"

open Term
def delabToDeclSigWithId (t : Term) (defKind : Bool) :
    TermElabM (TSyntax ``declId × TSyntax (if defKind then ``optDeclSig else ``declSig)) := do
  let (type, levelParams, newName) ← do
    if let `(term|$id:ident) := t then
      let n ← resolveGlobalConstNoOverload id
      let info ← getConstInfo n
      pure (info.type, info.levelParams, id.getId.appendAfter "'")
    else
      let e ← elabTerm t none
      synthesizeSyntheticMVarsNoPostponing
      let type ← inferType e
      pure (type, [], `foo)
  -- TODO: could use the infos for hovers here
  let (sig, _) ← delabCore type (delab := delabForallParamsWithSignature fun groups type => do
    show DelabM <| TSyntax (if defKind then ``optDeclSig else ``declSig) from do
      if h : defKind then
        let stx ← `(optDeclSig| $groups* : $type)
        pure <| by simp only [h]; exact stx
      else
        let stx ← `(declSig| $groups* : $type)
        pure <| by simp only [h]; exact stx)
  let id ← if levelParams.isEmpty then
      `(declId| $(mkIdent newName))
    else
      `(declId| $(mkIdent newName).{$(levelParams.toArray.map Lean.mkIdent),*})
  return (id, sig)

open Meta.Tactic.TryThis in
elab_rules : command
| `(declarationLike| $_ $d:defLike) => liftTermElabM do
  let `(defLike| def_like $t:term) := d | throwUnsupportedSyntax
  let (id, sig) ← delabToDeclSigWithId t true
  let declStx ← `(declaration| def $id:declId $sig:optDeclSig := sorry)
  addSuggestion d declStx
| `(declarationLike| $_ $d:theoremLike) => liftTermElabM do
  let `(theoremLike| theorem_like $t:term) := d | throwUnsupportedSyntax
  let (id, sig) ← delabToDeclSigWithId t false
  let declStx ← `(declaration| theorem $id:declId $sig:declSig := sorry)
  addSuggestion d declStx

end defLike

namespace Lean.Elab.Command

-- Alternate: ExceptLast type synonym with iterators and forin

@[specialize f]
def _root_.List.forAllButLastM {m} [Monad m] {α} (f : α → m Unit) : List α → m Unit
  | [] | [_] => pure ()
  | x :: xs => do f x; xs.forAllButLastM f

@[specialize f]
def _root_.List.forAllButLastM? {m} [Monad m] {α} (f : α → m Unit) : List α → m (Option α)
  | []  => return none
  | [x] => return x
  | x :: xs => do f x; xs.forAllButLastM? f

@[specialize f]
def _root_.List.foldAllButLastM {m} [Monad m] {α β} (f : α → β → m α) (init : α) : List β → m α
  | [] | [_] => pure init
  | x :: xs => do xs.foldAllButLastM f (← f init x)

@[specialize f]
def _root_.List.foldAllButLastM? {m} [Monad m] {α β} (f : α → β → m α) (init : α) :
    List β → m (α × Option β)
  | []  => return (init, none)
  | [x] => return (init, x)
  | x :: xs => do xs.foldAllButLastM? f (← f init x)

def _root_.List.dropAllButLast {α} : List α → List α
  | l@([]) | l@([_])  => l
  | _ :: xs => xs.dropAllButLast

def setScopes (scopes : List Scope) : CommandElabM Unit := modify ({· with scopes })

def dropScopes (n : Nat) : CommandElabM Unit :=
  modify fun s => { s with scopes := s.scopes.drop n }

@[specialize f]
def unzipScopesAuxM (f : Scope → CommandElabM Unit) (revAccScopes : List Scope) :
    List Scope → CommandElabM (List Scope × Scope)
  | [] => throwError "Encountered an empty list of scopes." -- !! Or use a "default" scope, `{ header := "", opts := ← getOptions }`?
  | [initialScope] => return (revAccScopes, initialScope)
  | scope :: rest => do f scope; unzipScopesAuxM f (scope :: revAccScopes) rest

def popAndReverseScopes : CommandElabM (List Scope × Scope) := do
  let revWithInit@(_, initScope) ← unzipScopesAuxM (fun _ => popScope) [] (← getScopes)
  modify ({ · with scopes := [initScope] })
  return revWithInit

def pushReversedScopesAux (newScopes : List Scope) : List Scope → CommandElabM (List Scope)
  | [] => return newScopes
  | scope :: revScopes => do pushScope; pushReversedScopesAux (scope :: newScopes) revScopes

def pushReversedScopes : List Scope → CommandElabM Unit
  | [] => return
  | revScopes => do
    let newScopes ← pushReversedScopesAux (← getScopes) revScopes
    modify ({· with scopes := newScopes })


-- def getResetScopes : CommandElabM (List Scope) := do
--   let savedScopes ← getScopes
--   let some initialScope ← savedScopes.forAllButLastM? fun _ => popScope
--     | throwError "Failed to find initial scope in `CommandElabM` state."
--   setScopes [initialScope]
--   return savedScopes

def throwNoInitialScope {α} : CommandElabM α :=
  throwError "Failed to find initial scope in `CommandElabM` state."

-- def getResetScopesTallied : CommandElabM (Nat × List Scope) := do
--   let savedScopes ← getScopes
--   let (n, some initialScope) ← savedScopes.foldAllButLastM? (init := 0) fun acc _ => do
--       popScope; return acc + 1
--     | throwNoInitialScope
--   setScopes [initialScope]
--   return (n, savedScopes)

abbrev PoppedRevScopes := List Scope

abbrev ScopeZipperCommandElabM := StateRefT PoppedRevScopes CommandElabM

nonrec def ScopeZipperCommandElabM.run {α} (x : ScopeZipperCommandElabM α)
    (poppedScopes : List Scope := []) := x.run poppedScopes
nonrec def ScopeZipperCommandElabM.run' {α} (x : ScopeZipperCommandElabM α)
    (poppedScopes : List Scope := []) := x.run' poppedScopes

namespace ScopeZipper

def unzipScope? : ScopeZipperCommandElabM (Option Scope) := do
  let scope :: scopes ← getScopes | throwNoInitialScope
  match scopes with
  | [] => return none -- `scope` is the initial scope, don't peel it
  | scopes => do
    popScope; setScopes scopes
    modifyThe PoppedRevScopes (scope :: ·)
    return scope

#check Scope
def zipScope? : ScopeZipperCommandElabM (Option Scope) := do
  let scope :: scopes ← getThe PoppedRevScopes | return none

  pushScope; modify ({ · })
  modifyThe PoppedRevScopes (scope :: ·)
  return scope

#check getAutoImplicits

end Lean.Elab.Command.ScopeZipper

def getVariableSyntax? : CommandElabM (Option (TSyntax ``Parser.Command.variable)) := do
  let { varDecls .. } ← getScope
  if varDecls.isEmpty then return none
  `(Parser.Command.variable| variable $varDecls*)

def getIncludeSyntax? : CommandElabM (Option (TSyntax ``Parser.Command.include)) := do
  let { includedVars .. } ← getScope
  if includedVars.isEmpty then return none
  -- TODO: the `Name`s are `varUIDs` with hygiene, but should we strip that in making the idents?
  `(Parser.Command.include| include $(includedVars.toArray.map mkIdent)*)

def getOmitSyntax? : CommandElabM (Option (TSyntax ``Parser.Command.omit)) := do
  let { omittedVars, varUIds, varDecls .. } ← getScope
  if omittedVars.isEmpty then return none
  let mut omittedIdentOrBinder : TSyntaxArray [`ident, `Lean.Parser.Term.instBinder] := #[]
  for var in omittedVars do
    for uid in varUIds, stx in varDecls do
      if uid = var then
        if stx.raw.isOfKind ``Parser.Term.instBinder then
          omittedIdentOrBinder := omittedIdentOrBinder.push ⟨stx.raw⟩
        else
          -- TODO: remove scopes?
          omittedIdentOrBinder := omittedIdentOrBinder.push (mkIdent uid)
        break
  -- TODO: the `Name`s are `varUIDs` with hygiene, but should we strip that in making the idents?
  `(Parser.Command.omit| omit $(omittedIdentOrBinder)*)

def _root_.Lean.Options.minus (opts minusOpts : Options) := Id.run do
  let mut opts := opts
  for (key, val) in minusOpts do
    let some minusVal := opts.get? key | continue
    if minusVal == val then
      opts := opts.erase key
  return opts

def getNewOptions : CommandElabM Options := do
  match ← getScopes with
  | scopes@h:(scope :: _ :: _) => do
    let initialScope := scopes.getLast (by grind)
    return scope.opts.minus initialScope.opts
  | _ => return {} -- if there is only the initial scope, there are no new options

def _root_.Lean.DataValue.toSetOptionValueSyntax? : DataValue → Option Syntax
  | .ofNat n      => Syntax.mkNumLit (toString n)
  | .ofBool b  => Syntax.atom .none (toString b)
  | .ofString str => Syntax.mkStrLit str
  | _ => none

def unreifyOptionValue? (val : Syntax) : Option DataValue :=
  match val.isStrLit? with
  | some str => some <| .ofString str
  | none     =>
  match val.isNatLit? with
  | some num => some <| .ofNat num
  | none     =>
  match val with
  | Syntax.atom _ "true"  => some <| .ofBool true
  | Syntax.atom _ "false" => some <| .ofBool false
  | _ => none

def _root_.Lean.Options.toSyntax (opts : Options) :
    CommandElabM (Array (TSyntax ``Parser.Command.set_option)) := do
  let mut optStx := #[]
  for (key, val) in opts do
    let some valStx := val.toSetOptionValueSyntax? | continue
    -- Note: this is a bit of a hack since it might be an `.atom`, and `TSyntax` only recognizes stra and num
    optStx := optStx.push <|← `(Parser.Command.set_option| set_option $(mkIdent key) $(⟨valStx⟩))
  return optStx

def getNewSetOptionSyntax : CommandElabM (Array (TSyntax ``Parser.Command.set_option)) := do
  (← getNewOptions).toSyntax

def getCurrNamespaceSyntax : CommandElabM (Option (TSyntax ``Parser.Command.namespace)) := do
  let ns ← getCurrNamespace
  if ns.isAnonymous then pure none else `(Parser.Command.namespace| namespace $(mkIdent ns))

inductive MergeResult where
  | new (openDecl : OpenDecl)
  | replace (openDecl : OpenDecl)


-- TODO: combine explicits and such. For now, just ignore preexisting ones.
def deduplicateOpenDecls (openDecls : List OpenDecl) : List OpenDecl :=
  -- Note that the innermost openDecls come first and affect name resolution first due to `eraseDups` affecting resolved ids by first occurrence (corresponding to later occurrences in openDecls)
  -- TODO: find something more efficient, which means basically just about anything else.
  openDecls.reverse.eraseDups.reverse

/-
Strategy: elabOpenDecl one by one?
-/

/-
Okay, so here's what I realized. We should just be maximally reifying. The integrated syntax with nice opens does *not* need to be the anonymous section syntax. They fulfill different roles.

-/


-- Exceptions:
-- Does not preserve full state stack, so end_local_scope won't work.
-- Does not preserve sections.
-- Does not preserve options set by default, deliberately. This could be changed for moving between projects
-- We *could* preserve this but it sounds awful.
-- TODO: switch order?
public section

-- TODO: prepend `_root_` instead of `@` for copy-paste affordance? Or discourage this to avoid making it easy to "hold it wrong"?
syntax reifiedExplicitOpenStx := ident " → " ident
-- TODO: wrap in parens for `hiding`? only technically unambiguous thanks to `@`.
syntax reifiedSimpleOpenStx := &"@" noWs ident
syntax reifiedSimpleOpenHidingStx := &"@" noWs ident " hiding " ident*
syntax reifiedOpenDecl := ppSpace colGt
  (reifiedSimpleOpenStx <|> ("(" reifiedSimpleOpenHidingStx <|> reifiedExplicitOpenStx ")"))
syntax reifiedOpenStx := withPosition("open" ppIndent(reifiedOpenDecl*))
syntax reifiedVarStx := Parser.Command.variable (ppLine Parser.Command.include)? (ppLine Parser.Command.omit)?
syntax reifiedOpenScopedDecl := ppSpace colGt &"@" noWs ident
syntax reifiedOpenScopedStx := withPosition("open " "scoped" ppIndent(reifiedOpenScopedDecl*))
syntax reifiedOptionKeyValue := ppSpace colGt ident ppSpace optionValue
syntax reifiedSetOptionsStx := withPosition("set_options " ppIndent(reifiedOptionKeyValue,*))

/--
A scope specification of the form
```
(@[expose])? (public)? (noncomputable)? (section)? scope
  (universe ...)?
  (namespace ...)?
  (open @id₁ @id₂ ...)?
  (open scoped @id₁ @id₂ ...)?
  (set_options key₁ val₁, key₂ val₂ ...)?
  (variable ...)?
  (include ...)?
  (omit ...)?
```
Currently, these must appear in order. Notice the differences from typical scope syntax.
-/
syntax scopeStx := Parser.Command.sectionHeader &"scope"
  (ppLine colGt Parser.Command.universe)?
  (ppLine colGt Parser.Command.namespace)?
  (ppLine colGt reifiedOpenStx)?
  (ppLine colGt reifiedOpenScopedStx)? -- TODO: local?
  (ppLine colGt reifiedSetOptionsStx)?
  (ppLine colGt reifiedVarStx)?

-- TODO: open scoped, etc.

partial def Lean.Syntax.merge! : Syntax → Syntax → Syntax
  | .node info `null args, .node _ `null #[] => .node info `null args
  | .node _ `null #[], .node info `null args => .node info `null args
  | .node info kind₁ args₁, .node _ _ args₂ =>
    .node info kind₁ (args₁.zipWith (·.merge!) args₂)
  | .missing, stx => stx
  | stx, _ => stx

def Bool.toDummyOptional? (b : Bool) : Option Syntax :=
  if b then some .missing else none

open Parser.Command in
def Lean.Elab.Command.Scope.toSectionHeader {m} [Monad m] [MonadQuotation m] :
    Scope → m (TSyntax ``sectionHeader)
  | { isPublic, isMeta, isNoncomputable, attrs .. } => do
    letI toDummyOptional? (b : Bool) : Option Syntax :=
      if b then some .missing else none
    let pubTk    := toDummyOptional? isPublic
    let metaTk   := toDummyOptional? isMeta
    let exposeTk := toDummyOptional? !attrs.isEmpty
    let ncTk     := toDummyOptional? isNoncomputable
    `(sectionHeader|
      $[@[expose%$exposeTk]]? $[public%$pubTk]? $[noncomputable%$ncTk]? $[meta%$metaTk]?)

def unreifySectionHeader (header : TSyntax ``Parser.Command.sectionHeader) : CommandElabM Unit :=
  match header with
  | `(Parser.Command.sectionHeader|
    $[@[expose%$exposeTk]]? $[public%$pubTk]? $[noncomputable%$ncTk]? $[meta%$metaTk]?) => do
    let isPublic := pubTk.isSome
    let isMeta := metaTk.isSome
    let attrs : List (TSyntax ``Parser.Term.attrInstance) ←
      if let some exposeTk := exposeTk then
        pure [← withRef exposeTk `(Parser.Term.attrInstance| expose)] else pure []
    let isNoncomputable := ncTk.isSome
    modifyScope fun s => { s with isPublic, isMeta, isNoncomputable, attrs }
  | _ => throwUnsupportedSyntax

def reifyOpenDecls {m} [Monad m] [MonadQuotation m] (openDecls : List OpenDecl) (dedup := true) :
    m (Option (TSyntax ``reifiedOpenStx)) := do
  let openDecls := if dedup then deduplicateOpenDecls openDecls else openDecls
  let reifiedOpens ← openDecls.foldrM (init := #[]) fun
    | .explicit id declName, acc => return acc.push <|←
      `(reifiedOpenDecl| ($(mkIdent id) → $(mkIdent declName)))
    | .simple ns except, acc => return acc.push <|←
      if except.isEmpty then `(reifiedOpenDecl| @$(mkIdent ns)) else
        let except := except.toArray.map mkIdent
        `(reifiedOpenDecl| (@$(mkIdent ns) hiding $except*))
  if reifiedOpens.isEmpty then return none else
    `(reifiedOpenStx| open $reifiedOpens*)

    -- let mut header : Syntax ← `(sectionHeader|)
    -- unless attrs.isEmpty do
    --   header.setArg
    -- if isPublic then
    --   header.setArg
    -- let metaTk? ← if isMeta then some <$> `(sectionHeader| meta) else pure none
    -- if attrs.isEmpty then
    --   `($pubTk?)

-- def getFullVariableSyntax

def Lean.Name.foldrPrefix {α} (n : Name) (init : α) (f : Name → α → α) :=
  let val := f n init
  match n with
  | .anonymous => val
  | .str pre _ | .num pre _ => pre.foldrPrefix val f

-- Looks at the parser extension's scopes. Might want to change this.
def _root_.Lean.Environment.activeScopes (env : Environment) : NameSet :=
  match Parser.parserExtension.ext.getState (asyncMode := .local) env |>.stateStack with
  | s :: _ => s.activeScopes
  | _ => {}

protected def _root_.Lean.Environment.extraScoped (env : Environment)
    (ns : Name) (openDecls : List OpenDecl) : NameSet := Id.run do
  let impliedScopes : List Name := openDecls.filterMap fun
    | .simple ns _ => some ns
    | _ => none
  let impliedScopes := ns.foldrPrefix (init := impliedScopes) fun n acc =>
    if n.isAnonymous then acc else acc.insert n
  -- what if we used just e.g. the `parserExtension`? or some other basic scopedEnvExtension? take it out of IO?
  return env.activeScopes.eraseMany impliedScopes -- TODO: make an iterator, this isn't great

def extraScoped : CommandElabM NameSet := do
  return (← getEnv).extraScoped (← getCurrNamespace) (← getScope).openDecls

def getUniverseStx : CommandElabM (Option <| TSyntax ``Parser.Command.universe) := do
  let levelNames := (← getScope).levelNames
  if levelNames.isEmpty then pure none else
    some <$> `(Parser.Command.universe| universe $(levelNames.toArray.map mkIdent)*)

def reifyScope : CommandElabM (TSyntax ``scopeStx) := do
  let sectionHeader ← (← getScope).toSectionHeader
  let universes ← getUniverseStx
  let namespaceStx ← getCurrNamespaceSyntax
  let opens ← reifyOpenDecls (← getScope).openDecls

  let variables ← (← getVariableSyntax?).mapM fun vars => do
    `(reifiedVarStx| $vars $(← getIncludeSyntax?)? $(← getOmitSyntax?)?)

  let extraScopedNames ← extraScoped
  let extraScoped ← if extraScopedNames.isEmpty then pure none else
    let extraScoped ← extraScopedNames.toArray.mapM fun n => `(reifiedOpenScopedDecl| @$(mkIdent n))
    some <$> `(reifiedOpenScopedStx| open scoped $extraScoped*)

  let newOpts ← getNewOptions -- TODO: actually, the base scope may be polluted, right? So maybe just list all of them.
  let setOptions ← do
    let mut kvs := #[]
    for (key, val) in newOpts do
      let some val := val.toSetOptionValueSyntax? | continue
      kvs := kvs.push <|← `(reifiedOptionKeyValue| $(mkIdent key) $(⟨val⟩))
    if kvs.isEmpty then pure none else some <$> `(reifiedSetOptionsStx| set_options $kvs,*)

  `(scopeStx| $sectionHeader scope
    $[$universes]?
    $[$namespaceStx]?
    $[$opens]?
    $[$extraScoped]?
    $[$setOptions]?
    $[$variables]?) -- TODO: technically the variable parsing could change if a scope is opened earlier. This is probably important...it'll mean (1) detecting if any variable syntax is scoped (2) writing a parser for `scope` that opens the named scopes!

    -- We also could account for `open (scoped) ... in variable` but it would have to be ad-hoc.

-- TODO: it's possible we should register these as namespaces if they are not already namesapces. I forget where that happens.
def unreifyOpenDecl (openDecl : TSyntax ``reifiedOpenDecl) (activateScopes := true) :
    CommandElabM OpenDecl :=
  match openDecl with
  | `(reifiedOpenDecl| @$id) => do
    if activateScopes then activateScoped id.getId
    return .simple id.getId []
  | `(reifiedOpenDecl| (@$id hiding $hidden*)) => do
    if activateScopes then activateScoped id.getId
    return .simple id.getId <| (hidden.map (·.getId)).toList
  | `(reifiedOpenDecl| ($id → $decl)) => return .explicit id.getId decl.getId
  | _ => throwUnsupportedSyntax

def _root_.Lean.OpenDecl.activate {m : Type → Type}
    [Monad m] [MonadEnv m] [MonadLiftT (ST IO.RealWorld) m] :
    OpenDecl → m Unit
  | .simple ns _  => activateScoped ns
  | .explicit _ _ => pure ()

def unreifyOpenDecls (openDeclsStx : TSyntaxArray ``reifiedOpenDecl) : CommandElabM Unit := do
  let openDecls ← openDeclsStx.foldlM (init := []) fun openDecls openDeclStx =>
    return (← unreifyOpenDecl openDeclStx) :: openDecls
  modifyScope fun s => { s with openDecls }

-- TODO: constinfo at decls
def unreifyScopeInBaseScope : TSyntax ``scopeStx → CommandElabM Unit
  | `(scopeStx| $sectionHeader scope
      $[universe $[$levelNames:ident]*]?
      $[$namespaceStx]?
      $[open $openDecls:reifiedOpenDecl*]?
      $[open scoped $openScopedDecls:reifiedOpenScopedDecl*]?
      $[set_options $keyVals:reifiedOptionKeyValue,*]?
      $[$vars]?) => do
    let [_] ← getScopes
      | throwError "Other scopes are active; expected no scopes to be active."
    -- TODO: check that it's "pure", i.e. actually the base scope?
    unreifySectionHeader sectionHeader
    if let some levelNames := levelNames then
      modifyScope fun s => { s with levelNames := levelNames.map (·.getId) |>.toList }
    if let some ns := namespaceStx then
      elabNamespace ns
    if let some openDecls := openDecls then
      unreifyOpenDecls openDecls
    if let some openScopedDecls := openScopedDecls then
      for openScoped in openScopedDecls do
        let `(reifiedOpenScopedDecl| @$id) := openScoped | throwUnsupportedSyntax
        activateScoped id.getId
    if let some keyVals := keyVals then
      for keyVal in keyVals.getElems do
        let `(reifiedOptionKeyValue| $id $val) := keyVal | throwUnsupportedSyntax
        -- Gets us info.
        let opts ← Elab.elabSetOption id val
        modifyScope fun s => { s with opts }
    if let some vars := vars then
      let `(reifiedVarStx| $vars $[$included]? $[$omitted]?) := vars | throwUnsupportedSyntax
      elabVariable vars
      if let some included := included then elabInclude included
      if let some omitted  := omitted  then elabOmit omitted
  | _ => throwUnsupportedSyntax

-- Next: spin it up, and trace influences, then skimmerize!
-- would be neat to create a visualization of all commands and how they link up that let you play with where they are. Maybe Claude could help with that, seeing as it's frontend stuff.

-- Integration is really next. We need to diff underneath `withoutModifyingScopesOrEnv`?

open Meta.Tactic.TryThis

syntax withPosition("show_current " colGt ("scope?" <|> scopeStx)) : command

elab_rules : command
| `(show_current scope?%$tk) => do
  liftCoreM <| addSuggestion tk <|← reifyScope
| `(show_current $reified:scopeStx) => do
  let scopeStx ← reifyScope
  unless scopeStx.raw.structEq reified do
    liftCoreM <| addSuggestion reified scopeStx

universe u

variable (x : Nat)

show_current public meta scope
  universe u
  open @Lean.Meta.Tactic.TryThis @Lean.Elab.Command @Lean.Elab @Lean
  variable (x : Nat)



#check List.dropAllButLast

def _root_.Lean.ScopedEnvExtension.popAllScopes {α β σ} (ext : ScopedEnvExtension α β σ) (env : Environment) :
    Environment :=
  ext.ext.modifyState (asyncMode := .local) env fun s =>
    match s.stateStack with
    | stack@(_ :: _ :: _) => { s with stateStack := stack.dropAllButLast }
    | _ => s

def popAllScopes {m : Type → Type} [Monad m] [MonadEnv m] [MonadLiftT (ST IO.RealWorld) m] :
    m Unit :=
  for ext in ← scopedEnvExtensionsRef.get do
    modifyEnv ext.popAllScopes

def getRevertAllScopes : CommandElabM (List Scope × Environment) := do
  let savedScopes ← getScopes; let env ← getEnv
  modify fun s => { s with scopes := s.scopes.dropAllButLast }
  popAllScopes
  return (savedScopes, env)

def resetScopes (pop := true) : CommandElabM Unit := do
  modify fun s => Id.run do
    let some headScope := s.scopes.getLast? | pure s
    -- TODO: we should read opts from the lakefile somehow
    { s with scopes := [{ header := headScope.header, opts := headScope.opts }] }
  if pop then popAllScopes

syntax withPosition("reset_to" ("(" &"pop" " := " &"false" ")")? ("scope?" <|> scopeStx)) : command

elab_rules : command
| `(reset_to $[(pop := false)]? scope?%$tk) => do
  liftCoreM <| addSuggestion tk <|← reifyScope
| `(reset_to $[(pop := false%$noPop)]? $reified:scopeStx) => do
  resetScopes noPop.isNone
  unreifyScopeInBaseScope reified

namespace Foo

def bar := true

-- reset_to public scope
--   universe u
--   namespace w
--   open @Foo
--   open scoped @Nat


def d : Type u := ULift Prop


open Bool hiding not



open Lean Elab Command

show_current public meta scope
  universe u
  namespace Foo
  open @Lean @Lean.Elab @Lean.Elab.Command @Lean.Meta.Tactic.TryThis (@Bool hiding not) @Lean
    @Lean.Elab @Lean.Elab @Lean.Elab.Command @Lean.Elab.Command @Lean.Elab.Command
  variable (x : Nat)



/-
1. integrate <scope>

2. #dependencies: Dependencies should work the following way.
- We need to treat current dependencies differently. We get the current file dependencies transitively. We stop at the first dependency not in the current module.
- We collect all the syntax nodekinds, look for originating files.
- We collect all elaborators from infotrees.
- We look at the new additions to the extraModUse etc.
- Future: tweak how it handles visibility

3. widget for going to line number, copying text?

4. extract scopes from below (open in etc.)?

5. file-level scope normalization.
- What exactly are the rules?
- How much dynamic trial-and-error do we have to do? `open X` too high can break things.

-/
  -- Add the relation (e.g. `GE.ge : Set Nat → Set Nat → Prop`) to the hover on the whole term

@[inline]
def withoutModifyingScopes {α} (x : CommandElabM α) : CommandElabM α := do
  let savedScopes ← getScopes
  try x finally modify ({· with scopes := savedScopes })

/-- Gets the topmost scope and current active scopes after unerifying `scopeStx`, without modifying the state. -/
def observeUnreifiedScopes (scopeStx : TSyntax ``scopeStx) : CommandElabM (Scope × NameSet) :=
  withoutModifyingScopes <| withoutModifyingEnv do
    resetScopes
    unreifyScopeInBaseScope scopeStx
    return (← getScope, (← getEnv).activeScopes)

structure ScopeDiff where
  newLevelNames : List Name
  -- new

-- class HDiff (α) (β) (γ) where
--   diff : α → β → γ


-- export HDiff (diff)

structure Diff (α : Type u) where
  added : α
  lost : α

class HasDiffType (α : Type u) where
  DiffType : Type u

export HasDiffType (DiffType)

-- currently everything diffs via `Diff`
instance {α} : HasDiffType α := ⟨Diff α⟩

class Diffable (α) [HasDiffType α] where
  diff : α → α → DiffType α

export Diffable (diff)

-- Hmm, might need to allow more parameters here. HDiff...how to "add them back"...


@[specialize f] -- TODO: or inline?
def Diff.map {α} {β} (f : α → β) : Diff α → Diff β
  | { added, lost } => { added := f added, lost := f lost }

@[specialize f]
def Diff.mapM {α} {β} {m} [Monad m] (f : α → m β) : Diff α → m (Diff β)
  | { added, lost } => return { added := ← f added, lost := ← f lost }

def _root_.List.diffByPrefix {α} [BEq α] : List α → List α → Diff (List α)
  | n@(nh :: nrest), m@(mh :: mrest) =>
    if nh == mh then nrest.diffByPrefix mrest else { added := n, lost := m }
  | n, m => { added := n, lost := m }

def _root_.Name.diff (new minus : Name) : Diff Name :=
  -- TODO: be better
  new.components.diffByPrefix minus.components |>.map (·.foldl (init := .anonymous) Name.append)

instance : Diffable Name := ⟨Name.diff⟩

def _root_.List.minus {α} [BEq α] (new minus : List α) : List α :=
  new.filter (!minus.contains ·)

-- def _root_.List.diff' {α} [BEq α] (new minus : List α) : Diff (List α) :=
--   { added := new.filter (!minus.contains ·), lost := minus.filter (!new.contains ·) }

#check unreifyOpenDecls

-- Strategy: have a certain effect, but report discrepancies.

universe v

syntax "#radicalize" ppLine command : command

/-- Reversed list of indices. Good for traversing. We assume indexing is fine. -/
abbrev SyntaxIndex := List Nat

variable (stx : Syntax) (n : Nat)

instance : GetElem Syntax SyntaxIndex Syntax (fun _ _ => True) where
  getElem stx path _ := path.foldr (init := stx) fun
    | i, .node _ _ args => args.getD i .missing
    | _, _ => .missing

structure TopDownWithIndex where
  firstChoiceOnly : Bool
  stx : Syntax
-- /--
-- `for _ in stx.topDown` iterates through each node and leaf in `stx` top-down, left-to-right.
-- If `firstChoiceOnly` is `true`, only visit the first argument of each choice node.
-- -/
def _root_.Lean.Syntax.topDownWithIdx (stx : Syntax) (firstChoiceOnly := false) : TopDownWithIndex :=
  ⟨firstChoiceOnly, stx⟩

partial instance {m} [Monad m] : ForIn m TopDownWithIndex (Syntax × SyntaxIndex) where
  forIn := fun ⟨firstChoiceOnly, stx⟩ init f => do
    let rec @[specialize] loop stx (idx : SyntaxIndex) b [Inhabited (type_of% b)] := do
      match (← f (stx, idx) b) with
      | ForInStep.yield b' =>
        let mut b := b'
        if let Syntax.node _ k args := stx then
          if firstChoiceOnly && k == choiceKind then
            return ← loop args[0]! (0 :: idx) b
          else
            for arg in args, i in 0...* do
              match (← loop arg (i :: idx) b) with
              | ForInStep.yield b' => b := b'
              | ForInStep.done b'  => return ForInStep.done b'
        return ForInStep.yield b
      | ForInStep.done b => return ForInStep.done b
    match (← @loop stx [] init ⟨init⟩) with
    | ForInStep.yield b => return b
    | ForInStep.done b  => return b

elab_rules : command
| `(#radicalize%$tk $cmd:command) => do
  let mut declIds := #[]
  let mut quickPosCheck := #[]
  let map ← getFileMap
  for stx in cmd.raw.topDown do
    if stx.isOfKind ``Parser.Command.declId then
      let some range := stx[0].getRange? | continue
        unless stx[0].getId.getRoot == rootNamespace do
          declIds := declIds.push (range, stx[0])
          quickPosCheck := quickPosCheck.push <| map.toPosition range.start
  elabCommand cmd
  if declIds.isEmpty then
    let toDelete := tk.getPos?.bind fun pos₁ => cmd.raw.getPos?.map fun pos₂ =>
      Syntax.ofRange ⟨pos₁, pos₂⟩
    liftCoreM <| addSuggestion tk ""
      (origSpan? := toDelete)
      (header := "No declaration names to replace; `#radicalize` may be removed.")
      (diffGranularity := .word)
      (codeActionPrefix? := "Delete #radicalize")
  else
    declIds := declIds.qsort (·.1.1 < ·.1.1)
    let mut loggedOnRadicalizeAlready := false
    for (n, { selectionRange .. }) in declRangeExt.getState (← getEnv) (asyncMode := .sync) do
      let sPos := selectionRange.pos
      if quickPosCheck.any (· = selectionRange.pos) then
        let range : Syntax.Range :=
          ⟨map.ofPosition selectionRange.pos, map.ofPosition selectionRange.endPos⟩
        -- TODO: is there a findErase?
        let some idx := declIds.findFinIdx? (·.1 == range) | continue
        let (_, declId) := declIds[idx]
        declIds := declIds.eraseIdx idx
        let n := privateToUserName n
        if (idx : Nat) = 0 then
          -- Also log it on the token for convenience.
          liftCoreM <| addSuggestion tk (origSpan? := declId) (toString <| rootNamespace ++ n)
          loggedOnRadicalizeAlready := true
        liftCoreM <| addSuggestion declId (toString <| rootNamespace ++ n)
    unless declIds.isEmpty do
      for (_, declId) in declIds do
        logWarningAt declId m!"`#radicalize` could not infer the full declaration name of {declId}."

show_current public meta scope
  universe v u
  namespace Foo
  open @Lean @Lean.Elab @Lean.Elab.Command @Lean.Meta.Tactic.TryThis (@Bool hiding not)
  variable (x : Nat) (stx : Syntax) (n : Nat)

reset_to scope

namespace Fooo

public def a := true

end Fooo

namespace Bar

public def a := false

end Bar

namespace Baz

public def a := false

end Baz

-- reset_to (pop := false) scope

-- #scopes

-- Because Lean

reset_to scope

open Fooo Bar Fooo Baz Bar

show_current scope
  open @Fooo @Bar @Baz

run_cmd do Lean.logInfo m!"{← Lean.resolveGlobalName `a }"

reset_to scope

open Bar Fooo Baz Fooo Baz Fooo


show_current scope
  open @Bar @Fooo @Baz

run_cmd do Lean.logInfo m!"{← Lean.resolveGlobalName `a }"

reset_to public meta scope
  universe v u
  namespace Foo
  open @Lean @Lean.Elab @Lean.Elab.Command @Lean.Meta.Tactic.TryThis (@Bool hiding not) @Lean
    @Lean.Elab @Lean.Elab @Lean.Elab.Command @Lean.Elab.Command @Lean.Elab.Command
  variable (x : Nat) (stx : Syntax) (n : Nat)

def dropNamespace (ns : Name) (check := false) : CommandElabM Unit := do
  if check then
    unless ns.isSuffixOf (← getCurrNamespace) do
      throwError "Expected `{ns}` to be a suffix of the current namespace `{← getCurrNamespace}`."
  modify fun s => { s with scopes := s.scopes.drop ns.getNumParts }
  for _ in 0...ns.getNumParts do popScope

def integrateScopes (scopeStx : TSyntax ``scopeStx) (exact := false) :
    CommandElabM ScopeDiff := do
  let (tgtScope, activeScopes) ← observeUnreifiedScopes scopeStx
  -- Suffix lost and suffix added
  let namespaceDiff := diff tgtScope.currNamespace (← getCurrNamespace)
  dropNamespace namespaceDiff.lost
  -- Sadly API is locked behind elab
  elabNamespace <|← `(namespace $(mkIdent namespaceDiff.added))

  let newLevelNames := tgtScope.levelNames.minus (← getLevelNames)


  -- let openDiff


-- Next up integrating, or tracing dependencies? Kind of like not just reify scopes, but extract. Hard to tell what matters for tactics and such though.

-- def getOpenDeclSyntax : CommandElabM
/-
# NEXT
So here's the current strategy:
- Try to reproduce just the current scope.
- Have a "check" phase where we try and compare scopes up to <something>. E.g. duplicated open decls are fine, different orderings...probably fine?
- If the check doesn't match, try to add `_root_` for any failing opens?
  - I think this means don't go for syntax too soon. Well...it's hard to track the errors.
  - Would be nice if every function could explain why it failed to something else.
- we switch to "condensed stack" mode where we recreate the whole stack.
- We can have a "full stack" mode that captures everything, including sections.

- Then there's a separate phase of "working" where the commands in our block may alter the scope, and we need to be prepared for that. Maybe on any `end` we switch to full stack? Can anything else pop a scope or modify scopes? `end_local_scoped`, right?


- Remember, the goal is integrating with other scopes.

Some edge cases:
- New declarations in the environment changed which namespaces we could resolve in `open`.

Interesting idea: a version of shake that goes further and completely restructures where declarations should live. But part of this is extending the "module use" recording to know which command is necessary.

Actually, would be great to *see* this instead. And drag little things around, maybe?


I'm now imagining a language in which this sort of change-such-that is first class. Everything is bidirectional, everything has a derivative, or some 2-categorical equipment that lets us say "find the thing which would create this thing..."
-/

#check Nat

-- Why doesn't regular `Nat` show up, and why does `Lean.Nat` show up twice? Scoping activated by `namespace`?
open Nat hiding add



def reifyScopeAux (acc : ReifiedScopeData)









/-
So we've got to remove scopes, then put them back locally, then put them back more broadly...

Well, we don't necessarily need the second, I guess. Or we could elaborate the command twice?

Actually...the whole point of `autonomous` would be to get it compiling in the next file. It's easy for it to be an `end_all`, but not a free-floating "island" whose effects nonetheless get merged into the subsequent declarations in the file.

Unless...we *restarted* all of the scopes after! We have the ability from the reification of scopes in `#autonomize`.

However, presumably, we eventually want to deduplicate/clean up...and so maybe we don't want to isolate it quite so much. "Seeing how it fares in the new environment" might be part of the goal.

----

Import dependency collection:
- the *new* extraModUses and indirectModUses, compared to the start of the command.
- infotree elsborators
- the transitive dependencies of new constants

Local dependency collection:
- syntax nodekinds
- infotree elaborators
- declarations used *before* the current command

There's a chance the original relies on alterations to environment extensions that cannot be reified. We just fail here.

There's a chance that we succeed but thanks to specifics of the initial state of env extensions. We can report the full imports, at least?

We must figure out which scopes are namespacey.

We must further figure out which scoped env extensions were activated *not* by namespacing or open decls, but by `open scoped`.

Must deduplicate names in open decls. But also keep them in order, since they may influence each other.

Ideally we eventually try to rearrange them and see if resolution is better.

We need to know what the current namespaces were when these were opened, too.

Note: namespaces do not open decls. But they do activate scopes and modify the scope stack. Sometimes multiple times in a row. These can be collected, but we need diffing. This diffing further needs to return a potentially dataful ignore, which may include e.g. a set_option.


Further, one can imagine getting the used imports, deduplicating as shake does, finding the right place in the hierarchy a la #find_home, getting toggles for imports and help integrating them...

The complexity of name resolution influence sourcing rears its head here: we don't know if an `export` statement influenced name resolution throughout.


For copy-pasting ease we do actually want root when possible, not just `end_all`. So find all the declaration selection ranges, etc. Can we replace a range?

e

-/
meta section

#check expandDeclId

universe u

partial def ppWithReprint (stx : Syntax) : Option String := do
  let mut s := ""
  for stx in stx.topDown (firstChoiceOnly := true) do
    match stx with
    | atom info val           => s := s ++ reprintLeaf info val
    | ident info rawVal _ _   => s := s ++ reprintLeaf info rawVal.toString
    | node _    kind args     =>
      if kind == choiceKind then
        -- this visit the first arg twice, but that should hardly be a problem
        -- given that choice nodes are quite rare and small
        let s0 ← reprint args[0]!
        for arg in args[1...*] do
          let s' ← reprint arg
          guard (s0 == s')
    | _ => pure ()
  return s
where
  reprintLeaf (info : SourceInfo) (val : String) : String :=
    match info with
    | SourceInfo.original lead _ trail _ => s!"{lead}{val}{trail}"
    -- no source info => add gracious amounts of whitespace to definitely separate tokens
    -- Note that the proper pretty printer does not use this function.
    -- The parser as well always produces source info, so round-tripping is still
    -- guaranteed.
    | _                                => s!" {val} "

elab tk:"#reprint" ppLine cmd:command : command => do
  liftCoreM <| Meta.Tactic.TryThis.addSuggestion tk cmd




end

#scopes

open ResolveName

run_cmd do
  logInfo m!"{resolveNamespaceUsingScope? (← getEnv) `Nat (← getCurrNamespace)}"
  logInfo m!"{resolveNamespaceUsingOpenDecls (← getEnv) `Nat [.simple `Lean []]}"

namespace Nat

#scopes

section foo

#scopes


elab "autonomous" ppLine colGe cmd:command : command => do
  let savedScopes ← getScopes
  popScope

def Nat.Bool : Type := Nat



variable (x : Bool) (y :   Nat) [Nonempty (Bool)]

def y := x

open Nat

def y' := x

open PrettyPrinter

set_option pp.rawOnError true
run_cmd do
  let varDecls := (← getScope).varDecls
  let varCmd ← `(command| variable $varDecls*)
  logInfo m!"{← liftCoreM <| ppCommand varCmd}"

elab "#autonomize" ppLine colGe cmd:command : command => do
  let savedScopes ← getScopes
