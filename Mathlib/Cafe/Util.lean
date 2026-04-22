module

public import Lean
public meta import Mathlib.Lean.MessageData.ForExprs

open Lean Elab Term Tactic Command


elab tk:"#show_stx" ppLine colGe cmd:command : command => do
  logInfoAt tk m!"{format cmd}"; elabCommand cmd
elab tk:"#show_stx!" ppLine colGe cmd:command : command => do
  logInfoAt tk m!"{repr cmd}"; elabCommand cmd

syntax (name := showTermStx) "#show_stx" colGe term : term
syntax (name := showTermStx!) "#show_stx!" colGe term : term
@[term_elab showTermStx] public meta def elabShowTermStx : TermElab := fun stx ty? => do
  logInfoAt stx[0] stx[1]; Term.elabTerm stx[1] ty?
@[term_elab showTermStx!] public meta def elabShowTermStx! : TermElab := fun stx ty? => do
  logInfoAt stx[0] stx[1]; Term.elabTerm stx[1] ty?

elab tk:"#show_stx" colGe tac:tactic : tactic => do
  logInfoAt tk m!"{format tac}"; evalTactic tac
elab tk:"#show_stx!" colGe tac:tactic : tactic => do
  logInfoAt tk m!"{repr tac}"; evalTactic tac

elab "#show_vars" : command => do
  logInfo m!"{(← getScope).varDecls}"

public meta section Repr

-- open Lean Meta Elab Parser PrettyPrinter Delaborator SubExpr Command

local instance : Repr Std.Format.FlattenBehavior := ⟨fun _ _ => f!"<flatten>"⟩

deriving instance Repr for Std.Format

instance : Repr Options where
  reprPrec opts _ := Id.run do
    let mut f := #[]
    for kv in opts do
      -- TODO: clean up
      unless f.isEmpty do f := f.push f!", "
      f := f.push f!"{kv}"
    return .bracket "{ " (f.foldl (init := .nil) (· ++ ·)) " }"

deriving instance Repr for OpenDecl, Scope

variable {α} [Repr α]

syntax "derive_recursively?" command* : command

open Meta
def tryCommandElseSuggest (cls : Name) (cmd : Command) : MetaM Unit := do
  try
    liftCommandElabM <| elabCommand cmd
    resetSynthInstanceCache
  catch ex => do
    let mut sugs := #[]
    for (ctx, e) in ex.toMessageData.exprs do
      for decl in e.getUsedConstants do
        if decl == cls then continue
        let d ← mkConstWithFreshMVarLevels decl
        let failed ← forallTelescope (← inferType expr) fun args _ => do
          let c ← mkConstWithFreshMVarLevels cls
          let fvarIds := (← getLCtx).getFVarIds.toList
          addLocalInstances cls (do
            trace[debug] "{(← getLCtx).getFVarIds.map Expr.fvar}, {(← getLocalInstances).map (·.className)}"
            if (← observing? <| Meta.checkApp c (mkAppN d args)).isSome then
              return (← synthInstance? <| c.app (mkAppN d args)).isNone
            else return false) fvarIds


elab_rules : command
| `(derive_recursively? $cmds*) => do
  for cmd in cmds do
    try

#synth Repr (Std.TreeMap FVarId α (Name.quickCmp ·.name ·.name))
deriving instance Repr for
  PersistentHashMap.Entry, PersistentHashMap.Node, PersistentHashMap,
  PersistentArrayNode, PersistentArray

deriving instance Repr for FVarIdMap α

deriving instance Repr for ExprConfigCacheKey, InfoCacheKey, ParamInfo, FunInfo
deriving instance Repr for LocalDecl, LocalInstance, LocalContext, MetavarDecl, DelayedMetavarAssignment, AbstractMVarsResult, SynthInstanceCacheKey
deriving instance Repr for Lean.Meta.DefEqCache
deriving instance Repr for Meta.InferTypeCache, FunInfoCache, SynthInstanceCache, DefEqCache
deriving instance Repr for Cache, MetavarContext, Meta.State

end Repr

elab "#scopes" : command => do
  logInfo m!"{repr <|← getScopes}"

elab "#constants"
