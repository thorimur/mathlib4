module

public import Lean




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

def _root_.Lean.DataValue.toSetOptionSyntax? : DataValue → Option Syntax
  | .ofNat n      => Syntax.mkNumLit (toString n)
  | .ofBool true  => Syntax.atom .none "true"
  | .ofBool false => Syntax.atom .none "true"
  | .ofString str => Syntax.mkStrLit str
  | _ => none

def _root_.Lean.Options.toSyntax (opts : Options) :
    CommandElabM (Array (TSyntax ``Parser.Command.set_option)) := do
  let mut optStx := #[]
  for (key, val) in opts do
    let some valStx := val.toSetOptionSyntax? | continue
    -- Note: this is a bit of a hack since it might be an `.atom`, and `TSyntax` only recognizes stra and num
    optStx := optStx.push <|← `(Parser.Command.set_option| set_option $(mkIdent key) $(⟨valStx⟩))
  return optStx

def getNewSetOptionSyntax : CommandElabM (Array (TSyntax ``Parser.Command.set_option)) := do
  (← getNewOptions).toSyntax

def getCurrNamespaceSyntax : CommandElabM (TSyntax ``Parser.Command.namespace) := do
  `(Parser.Command.namespace| namespace $(mkIdent <|← getCurrNamespace))

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
