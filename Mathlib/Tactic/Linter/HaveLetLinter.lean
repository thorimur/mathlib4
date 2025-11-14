/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import Mathlib.Init
import Lean.Elab.Command
import Lean.Server.InfoUtils
import Mathlib.Tactic.DeclarationNames

/-!
# The `have` vs `let` linter

The `have` vs `let` linter flags uses of `have` to introduce a hypothesis whose Type is not `Prop`.

The option for this linter is a natural number, but really there are only 3 settings:
* `0` -- inactive;
* `1` -- active only on noisy declarations;
* `2` or more -- always active.

TODO:
* Also lint `let` vs `have`.
* `haveI` may need to change to `let/letI`?
* `replace`, `classical!`, `classical`, `tauto` internally use `have`:
  should the linter act on them as well?
-/

open Lean Elab Command Meta

namespace Mathlib.Linter

/-- The `have` vs `let` linter emits a warning on `have`s introducing a hypothesis whose
Type is not `Prop`.
There are three settings:
* `0` -- inactive;
* `1` -- active only on noisy declarations;
* `2` or more -- always active.

The default value is `1`.
-/
register_option linter.haveLet : Nat := {
  defValue := 0
  descr := "enable the `have` vs `let` linter:\n\
            * 0 -- inactive;\n\
            * 1 -- active only on noisy declarations;\n\
            * 2 or more -- always active."
}

namespace haveLet

/-- find the `have` syntax. -/
def isHave? : Syntax → Bool
  | .node _ ``Lean.Parser.Tactic.tacticHave__ _ => true
  | _ => false

end haveLet

end Mathlib.Linter

namespace Mathlib.Linter.haveLet

/-- a monadic version of `Lean.Elab.InfoTree.foldInfo`.
Used to infer types inside a `CommandElabM`. -/
def InfoTree.foldInfoM {α m} [Monad m] (f : ContextInfo → Info → α → m α) (init : α) :
    InfoTree → m α :=
  InfoTree.foldInfo (fun ctx i ma => do f ctx i (← ma)) (pure init)

/-- given a `ContextInfo`, a `LocalContext` and an `Array` of `Expr`essions `es` with a `Name`,
`toFormat_propTypes` creates a `MetaM` context, and returns an array of
the pretty-printed `Format` of `e`, together with the (unchanged) name
for each `Expr`ession `e` in `es` whose type is a `Prop`.

Concretely, `toFormat_propTypes` runs `inferType` in `CommandElabM`.
This is the kind of monadic lift that `nonPropHaves` uses to decide whether the Type of a `have`
is in `Prop` or not.
The output `Format` is just so that the linter displays a better message. -/
def toFormat_propTypes (ctx : ContextInfo) (lc : LocalContext) (es : Array (Expr × Name)) :
    CommandElabM (Array (Format × Name)) := do
  ctx.runMetaM lc do
    es.filterMapM fun (e, name) ↦ do
      let typ ← inferType (← instantiateMVars e)
      if typ.isProp then return none else return (← ppExpr e, name)

/-- returns the `have` syntax whose corresponding hypothesis does not have Type `Prop` and
also a `Format`ted version of the corresponding Type. -/
partial
def nonPropHaves : InfoTree → CommandElabM (Array (Syntax × Format)) :=
  InfoTree.foldInfoM (init := #[]) fun ctx info args => return args ++ (← do
    let .ofTacticInfo i := info | return #[]
    let stx := i.stx
    let .original .. := stx.getHeadInfo | return #[]
    unless isHave? stx do return #[]
    let mctx := i.mctxAfter
    let mvdecls := i.goalsAfter.filterMap (mctx.decls.find? ·)
    -- We extract the `MetavarDecl` with largest index after a `have`, since this one
    -- holds information about the metavariable where `have` introduces the new hypothesis,
    -- and determine the relevant `LocalContext`.
    let lc := mvdecls.toArray.getMax? (·.index < ·.index) |>.getD default |>.lctx
    -- we also accumulate all `fvarId`s from all local contexts before the use of `have`
    -- so that we can then isolate the `fvarId`s that are created by `have`
    let oldMvdecls := i.goalsBefore.filterMap (mctx.decls.find? ·)
    let oldFVars := (oldMvdecls.map (·.lctx.decls.toList.reduceOption)).flatten.map (·.fvarId)
    -- `newDecls` are the local declarations whose `FVarID` did not exist before the `have`.
    -- Effectively they are the declarations that we want to test for being in `Prop` or not.
    let newDecls := lc.decls.toList.reduceOption.filter (! oldFVars.contains ·.fvarId)
    -- Now, we get the `MetaM` state up and running to find the types of each entry of `newDecls`.
    -- For each entry which is a `Type`, we print a warning on `have`.
    let fmts ← toFormat_propTypes ctx lc (newDecls.map (fun e ↦ (e.type, e.userName))).toArray
    return fmts.map fun (fmt, na) ↦ (stx, f!"{na} : {fmt}"))

/-- The main implementation of the `have` vs `let` linter. -/
def haveLetLinter : Linter where run := withSetOptionIn fun _stx => do
  let gh := linter.haveLet.get (← getOptions)
  unless gh != 0 && (← getInfoState).enabled do
    return
  unless gh == 1 && (← MonadState.get).messages.unreported.isEmpty do
    let trees ← getInfoTrees
    for t in trees do
      for (s, fmt) in ← nonPropHaves t do
        logLint0Disable linter.haveLet s
          m!"'{fmt}' is a Type and not a Prop. Consider using 'let' instead of 'have'."

initialize addLinter haveLetLinter

end haveLet

end Mathlib.Linter

namespace Lean.Elab.InfoTree


/--
Finds the first result of `f ctx info children` which is `some a`, descending the
tree from the top. Merges and updates contexts as it descends the tree.

If provided, `ctx?` is used as an initial context. This can be helpful when invoking `findSome?` in
the middle of a larger traversal.
-/
partial def findSome? {α} (f : ContextInfo → Info → PersistentArray InfoTree → Option α)
    (t : InfoTree) (ctx? : Option ContextInfo := none) : Option α :=
  go ctx? t
where go ctx?
  | context ctx t => go (ctx.mergeIntoOuter? ctx?) t
  | node i ts =>
    let a := match ctx? with
      | none => none
      | some ctx => f ctx i ts
    a <|> ts.findSome? (go <| i.updateContext? ctx?)
  | hole _ => none

/--
Returns the value of `f ctx info children` on the outermost `.node info children` which has
context, having merged and updated contexts appropriately.

If provided, `ctx?` is used as an initial context. This can be helpful when invoking `onFirstNode?`
in the middle of a larger traversal.
-/
def onFirstNode? {α} (t : InfoTree) (f : ContextInfo → Info → PersistentArray InfoTree → α)
    (ctx? : Option ContextInfo := none) : Option α :=
  t.findSome? (ctx? := ctx?) fun ctx i ch => some (f ctx i ch)

def getTopInfo? : InfoTree → Option Info
| .context _ i => getTopInfo? i
| .hole _ => none
| .node i _ => some i


def getTopNode? (t : InfoTree) (ctx? : Option ContextInfo := none) : Option (ContextInfo × Info × PersistentArray InfoTree) :=
  t.onFirstNode? (ctx? := ctx?) (·,·,·)


/--
Get the `parentDecl`s of every elaborated body. This includes `let rec`/`where`
definitions. Assumes that every declaration elaboration proceeds through `Lean.Elab.Term.BodyInfo`.
-/
def getDeclsByBody (t : InfoTree) :
    CommandElabM (List (Option Name × Option Nat × Bool × Option Format)) :=
  t.collectNodesBottomUpM fun ctx i ch decls =>
    match i with
    | .ofCustomInfo i =>
      if i.value.typeName == ``Lean.Elab.Term.BodyInfo then do
        let decl := ctx.parentDecl?
        let ch := ch.filter fun t => !t.getTopInfo? matches (some (.ofPartialTermInfo _))
        if ch.size != 1 then
          return (decl, some ch.size, false, none) :: decls
        else
          if let some (ctx, info, _) := ch[0]!.getTopNode? ctx then
            if info matches .ofTermInfo _ || info matches .ofTacticInfo _ then
              return decls
            else
              return (decl, none, true, some (← info.format ctx)) :: decls
          else do
            -- let fmt ← ch.foldlM (init := f!"[") fun fmt t => do
            --   let f' ← t.format ctx
            --   return fmt ++ f' ++ f!"];;["
            let fmt ← match ch[0]! with
              | .context .. => pure f!"context"
              | .hole .. => pure "hole"
              | .node i _ => i.format ctx
            return (decl, none, false, some fmt) :: decls
      else return decls
    | _ => return decls


/-- Collects all `parentDecl`s that appear at any point throughout the infotree. -/
partial def getDeclsByParent (t : InfoTree) : NameSet :=
  go {} t
where
  /-- Visits all subinfotrees and collects `PartialContextInfo.parentDeclCtx`s directly. -/
  go acc : InfoTree → NameSet
  | .context (.parentDeclCtx decl) i => go (acc.insert decl) i
  | .context _ i => go acc i
  | node _ ch => ch.foldl (init := acc) go
  | .hole _ => acc

-- .mergeSort fun n m => n.quickCmp m |>.isLE
def compareDecl : Linter where
  run stx := do
    for t in ← getInfoTrees do
      let decls ← t.getDeclsByBody
      -- let parents := t.getDeclsByParent.toList
      if !decls.isEmpty then
        logInfo m!"got:\ndecls: {decls}"

      -- unless bodies == parents do

initialize addLinter compareDecl

end Lean.Elab.InfoTree
