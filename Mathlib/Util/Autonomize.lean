module

public import Lean

/-!
# `#autonomize` for isolating declarations from their scopes

`#autonomize` suggests a modification to the following declaration syntax that isolates it from the surrounding scopes.

## Implementation details

We need to include the following:

```
autonomous
(@[$attrs*])? (public)? (meta)? section -- only if any isSome
(namespace $currNamespace)?

```

I'm wondering if we need to decouple the API for `Scope`s in the state from the API for environment extension scopes. I mean, can we literally just store the whole stack and reset the state, instead of worrying about pushScope and popScope?

TODO: notation and syntax that's used, dependencies in the current file, dependencies on environment extension states...
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
