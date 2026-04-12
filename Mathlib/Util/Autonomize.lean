module

public import Lean
public meta import Lean.Elab.BuiltinCommand
public meta import Lean.PrettyPrinter.Delaborator
import Batteries

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
def deduplicateOpenDecls (openDecls : List OpenDecl) : Array OpenDecl :=
  -- Note that the innermost openDecls come first, so we `foldr` to give earlier opens precedence.
  openDecls.foldr (init := #[]) fun openDecl acc =>
    if acc.contains openDecl then acc else acc.push openDecl

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
syntax reifiedExplicitOpenStx := "(" ident " → " ident ")"
syntax reifiedSimpleOpenStx := &" @" noWs ident (" hiding " ident*)?
syntax reifiedOpenDecl := reifiedSimpleOpenStx <|> reifiedExplicitOpenStx
syntax reifiedOpenStx := "open " reifiedOpenDecl*
syntax reifiedVarStx := Parser.Command.variable (ppLine Parser.Command.include)? (ppLine Parser.Command.omit)?
syntax reifiedOpenScopedDecl := &"@" noWs ident
syntax reifiedOpenScopedStx := "open" ppSpace "scoped" reifiedOpenScopedDecl*
syntax reifiedOptionKeyValue := ident ppSpace optionValue
syntax reifiedSetOptionsStx := "set_options " reifiedOptionKeyValue,*

syntax scopeStx := Parser.Command.sectionHeader &"scope" ppIndent(
  (ppLine Parser.Command.universe)?
  (ppLine Parser.Command.namespace)?
  (ppLine reifiedOpenStx)?
  (ppLine reifiedOpenScopedStx)? -- TODO: local?
  (ppLine reifiedSetOptionsStx)?
  (ppLine reifiedVarStx)?)

syntax "anonymous " scopeStx ppLine "in " "section" command : command

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

def reifyOpenDecls {m} [Monad m] [MonadQuotation m] (openDecls : List OpenDecl) :
    m (Option (TSyntax ``reifiedOpenStx)) := do
  let reifiedOpens ← openDecls.foldrM (init := #[]) fun
    | .explicit id declName, acc => return acc.push <|←
      `(reifiedOpenDecl| ($(mkIdent id) → $(mkIdent declName)))
    | .simple ns except, acc => return acc.push <|←
      if except.isEmpty then `(reifiedOpenDecl| @$(mkIdent ns)) else
        let except := except.toArray.map mkIdent
        `(reifiedOpenDecl| @$(mkIdent ns) hiding $except*)
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

protected def IO.extraScoped (env : Environment) (ns : Name) (openDecls : List OpenDecl) :
    IO NameSet := do
  let impliedScopes : List Name := openDecls.filterMap fun
    | .simple ns _ => some ns
    | _ => none
  let impliedScopes := ns.foldrPrefix (init := impliedScopes) fun n acc =>
    if n.isAnonymous then acc else acc.insert n
  -- what if we used just e.g. the `parserExtension`? or some other basic scopedEnvExtension? take it out of IO?
  let some first := (← scopedEnvExtensionsRef.get)[0]? | return {}
  let s :: _ := first.ext.getState env |>.stateStack | return {}
  return s.activeScopes.eraseMany impliedScopes -- TODO: make an iterator, this isn't great


def extraScoped : CommandElabM NameSet := do
  IO.extraScoped (← getEnv) (← getCurrNamespace) (← getScope).openDecls

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

def unreifyOpenDecl : TSyntax ``reifiedOpenDecl → CommandElabM OpenDecl
  | `(reifiedSimpleOpenStx| @$id $[hiding $hidden*]?) => do
    let except := if let some hidden := hidden then hidden.map (·.getId) |>.toList else []
    activateScoped id.getId
    return .simple id.getId except
  | `(reifiedExplicitOpenStx| ($id → $decl)) => return .explicit id.getId decl.getId
  | _ => throwUnsupportedSyntax

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

syntax "show_current " ("scope?" <|> scopeStx) : command

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
    open @Lean @Lean.Elab @Lean.Elab.Command @Lean.Meta.Tactic.TryThis
    variable (x : Nat)

syntax "reset_to" ("scope?" <|> scopeStx) : command

#check MessageData.signature

open Lean
#check Parser.Command.declaration
syntax defLike := "def_like " term
syntax theoremLike := "theorem_like " term
-- syntax instanceLike := "instance_like " ident
syntax (name := declarationLike) Parser.Command.declModifiersF
  (defLike <|> theoremLike) : command

-- def suggestDeclWithType (n : Name) : CommandElabM Name := do


open Lean Meta Elab Parser PrettyPrinter Delaborator SubExpr Command

instance : Repr Std.Format.FlattenBehavior := ⟨fun _ _ => f!"<flatten>"⟩

deriving instance Repr for Std.Format

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

def getResetScopes : CommandElabM (List Scope × Environment) := do
  let savedScopes ← getScopes; let env ← getEnv
  modify fun s => { s with scopes := s.scopes.dropAllButLast }
  popAllScopes
  return (savedScopes, env)

def resetScopes : CommandElabM Unit := do
  modify fun s => { s with scopes := s.scopes.dropAllButLast }
  popAllScopes


elab_rules : command
| `(reset_to scope?%$tk) => do
  liftCoreM <| addSuggestion tk <|← reifyScope
| `(reset_to $reified:scopeStx) => do
  let
  liftCoreM <| addSuggestion tk (scopeStx)


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

#reprint
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
