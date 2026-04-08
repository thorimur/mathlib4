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
