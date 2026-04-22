module

public import Lean
public meta import Mathlib.Lean.MessageData.ForExprs
-- import all Lean.Environment
-- import all Init.Prelude

open Lean Elab Term Command

public meta section

syntax "deriving_recursively " "instance " ident " for " term,+ : command
open Meta
def addLocalInstances (cls : Name) {β} (x : MetaM β) : List FVarId → MetaM β
  | fvar :: rest => do
    let c ← mkConstWithFreshMVarLevels cls
    let b? : Option β ← do
      try
        Meta.checkApp c (.fvar fvar)
        pure none
      catch _ =>
        some <$> addLocalInstances cls x rest
    b?.getDM do
      withLocalDecl (← mkFreshBinderName) .instImplicit (c.app (.fvar fvar)) fun _ => do
        addLocalInstances cls x rest
  | [] => x

def deriveInstancesInExpr (expr : Expr) (cls : Name) (encountered : NameSet) : MetaM (NameSet × Array Command) := do
  let mut synthFailures := #[]
  -- let mut enc := encountered
  for decl in expr.getUsedConstants do
    -- if enc.contains decl then continue
    if decl == cls then continue
    unless (← getEnv).contains decl do continue
    if (← try isInstance decl catch _ => pure true) then continue

    let d ← mkConstWithFreshMVarLevels decl
    -- unless (← whnf <|← inferType d).isSort do
    --   trace[debug] "got {(← whnf <|← inferType d)} for {d}"
    --   continue
    let failed ← forallTelescope (← inferType d) fun args _ => do
      let c ← mkConstWithFreshMVarLevels cls
      let fvarIds := (← getLCtx).getFVarIds.toList
      addLocalInstances cls (do
        -- trace[debug] "{(← getLCtx).getFVarIds.map Expr.fvar}, {(← getLocalInstances).map (·.className)}"
        if (← observing? <| Meta.checkApp c (mkAppN d args)).isSome then
          return (← try synthInstance? <| c.app (mkAppN d args) catch _ => pure none).isNone
        else return false) fvarIds
    if failed then
      synthFailures := synthFailures.push decl
    -- trace[debug] m!"{cls} for {.ofConstName decl} in {expr} ↦ {e}"
    -- enc := enc.insert decl
  return ({}, ← synthFailures.mapM fun decl =>
    `(deriving instance $(mkIdent cls):term for $(mkIdent <| privateToUserName decl)))

def toLocalInstances (lctx : LocalContext) : MetaM LocalInstances := do
  let mut localInstances := #[]
  for decl in lctx do
    unless decl.isImplementationDetail do
      if let some className ← withReader ({ · with localInstances }) (Meta.isClass? decl.type) then
        localInstances := localInstances.push { className, fvar := decl.toExpr }
  return localInstances

def withPopulatingLocalInstances {α} (k : MetaM α) : MetaM α := do
  let localInstances ← toLocalInstances (← getLCtx)
  withReader ({ · with localInstances }) k

syntax (name := neededCmd) "#needed " command : command
partial def deriveRecursively (e : Expr) (cls : Name) (max curr : Nat) (needed : Array Command) (encountered : NameSet) : MetaM (NameSet × Array Command) := do
  if max < curr then throwError m!"Hit max depth at {e}, {cls}:\n\
    {m!"\n".joinSep (needed.map (m!"{·}")).toList}"; return (encountered, needed)
  trace[debug] "Looking at {e}, {cls}"
  let (encountered, derivings) ← deriveInstancesInExpr e cls encountered
  trace[debug] "trying {derivings}"
  let rec tryStx (stx : Command) (curr) (encountered : NameSet) (needed : Array Command) : MetaM (NameSet × Array Command) := do
    try
      -- let tr ← getTraceState
      try
        liftCommandElabM <| elabCommand stx
      catch ex =>
        throw ex
      finally
        resetSynthInstanceCache
      return (encountered, needed.push stx)
      -- setTraceState tr
    catch ex => do
      trace[debug] "Hit an error: {ex.toMessageData}."
      let mut encountered := encountered
      let mut needed := needed
      let nsize := needed.size
      for (ctx,expr) in ex.toMessageData.exprs do
        (encountered, needed) ← withLCtx' ctx.lctx <| withPopulatingLocalInstances <| deriveRecursively expr cls max (curr+1) needed encountered

      -- let tr ← getTraceState
      if (needed.filter (!·.raw.isOfKind ``neededCmd) |>.size) > nsize then
        tryStx stx (curr +1) encountered needed
      else
        return (encountered, needed.push <|← `(#needed $stx))

  let mut encountered := encountered
  let mut needed := needed
  for stx in derivings do
    (encountered, needed) ← tryStx stx curr encountered needed
  return (encountered, needed)
      -- setTraceState tr

elab_rules : command
| `(#needed $cmd) => do
  liftCoreM <| Tactic.TryThis.addSuggestion (← getRef) cmd
  elabCommand cmd


syntax withPosition("#all" (ppLine colEq command)*) : command


elab_rules : command
| `(deriving_recursively%$tk instance $id:ident for $t:term,*) => do
  let id ← resolveGlobalConstNoOverload id
  liftTermElabM do
    let mut encountered := {}
    let mut needed := #[]
    for t in (← t.getElems.mapM fun t => elabTerm t none) do
      (encountered, needed) ← deriveRecursively t id 30 0 needed encountered
    Meta.Tactic.TryThis.addSuggestion (← getRef) (←
    `(#all
      $needed*))

open Meta

variable (α) (β) [BEq α] [Hashable α] [Repr β]

macro "stub_repr " t:term : command => do
  let some str := t.raw.reprint | Macro.throwError "Could not reprint {t}"
  let str := Syntax.mkStrLit s!"<{str.trimAscii}>"
  `(instance : Repr $t := ⟨fun _ _ => $str:term⟩)

-- #synth Repr (PersistentHashMap α β)

-- deriving instance Repr for Lean.PersistentHashMap

-- #synth Repr (∀ α [Repr α] [BEq α] [Hashable α] β [Repr β] , PersistentHashMap α β)

deriving instance Repr for PersistentHashMap.Entry, PersistentHashMap.Node, PersistentHashMap
variable (α : Type) [Repr α] in
deriving instance Repr for FVarIdMap α
deriving instance Repr for Lean.LocalDecl
deriving instance Repr for Lean.PersistentArrayNode
deriving instance Repr for Lean.PersistentArray
deriving instance Repr for Lean.LocalContext
deriving instance Repr for Lean.LocalInstance
deriving instance Repr for Lean.LocalInstances
deriving instance Repr for Lean.MetavarDecl
deriving instance Repr for Lean.DelayedMetavarAssignment
deriving instance Repr for Lean.MetavarContext
deriving instance Repr for Lean.Meta.ExprConfigCacheKey
deriving instance Repr for Lean.Meta.InferTypeCache
deriving instance Repr for Lean.Meta.InfoCacheKey
deriving instance Repr for Lean.Meta.ParamInfo
deriving instance Repr for Lean.Meta.FunInfo
deriving instance Repr for Lean.Meta.FunInfoCache
deriving instance Repr for Lean.Meta.SynthInstanceCacheKey
deriving instance Repr for Lean.Meta.AbstractMVarsResult
deriving instance Repr for Lean.Meta.SynthInstanceCache
deriving instance Repr for Lean.Meta.DefEqCacheKey
deriving instance Repr for Lean.Meta.DefEqCache
deriving instance Repr for Lean.Meta.Cache
deriving instance Repr for Lean.FVarIdSet
deriving instance Repr for Lean.Meta.DefEqContext
deriving instance Repr for Lean.Meta.PostponedEntry
deriving instance Repr for Std.Format.FlattenBehavior
deriving instance Repr for Std.Format
deriving instance Repr for Lean.Elab.ElabInfo
deriving instance Repr for Lean.Elab.TacticInfo
deriving instance Repr for Lean.Elab.TermInfo
deriving instance Repr for Lean.Elab.PartialTermInfo
deriving instance Repr for Lean.Elab.CommandInfo
deriving instance Repr for Lean.Elab.MacroExpansionInfo
deriving instance Repr for Lean.Elab.OptionInfo
deriving instance Repr for Lean.Elab.ErrorNameInfo
deriving instance Repr for Lean.Elab.FieldInfo
deriving instance Repr for Lean.Elab.CompletionInfo

instance : Repr Dynamic where
  reprPrec d _ := f!"<Dynamic[{d.typeName}]"

instance : Repr Options where
  reprPrec opts _ := Id.run do
    let mut kvs : Array Format := #[]
    for kv in opts do
      kvs := kvs.push f!"{kv}"
    return .bracket "{" (f!", ".joinSep kvs.toList) "}"

-- #needed deriving instance Repr for StateT
-- #needed deriving instance Repr for StateM
deriving instance Repr for Lean.Lsp.RpcRef
deriving instance Repr for Lean.Server.ReferencedObject
deriving instance Repr for Lsp.RpcWireFormat
deriving instance Repr for Lean.Server.RpcObjectStore
deriving instance Repr for Lean.Json

open Lean.Widget in
stub_repr WidgetInstance

deriving instance Repr for Lean.Elab.UserWidgetInfo
deriving instance Repr for Lean.Elab.CustomInfo
deriving instance Repr for FVarAliasInfo
deriving instance Repr for Lean.Elab.FieldRedeclInfo
deriving instance Repr for Lean.Elab.DelabTermInfo
deriving instance Repr for Lean.Elab.ChoiceInfo
deriving instance Repr for Lean.Elab.DocInfo
deriving instance Repr for Lean.Elab.DocElabInfo
deriving instance Repr for Lean.Elab.Info

deriving instance Repr for Lean.PrettyPrinter.InfoPerPos
deriving instance Repr for Lean.FormatWithInfos
-- deriving instance Repr for Lean.VisibilityMap
deriving instance Repr for Lean.ConstantVal
deriving instance Repr for Lean.AxiomVal

deriving instance Repr for Lean.ReducibilityHints
deriving instance Repr for Lean.DefinitionVal
deriving instance Repr for Lean.TheoremVal
deriving instance Repr for Lean.OpaqueVal
deriving instance Repr for Lean.QuotKind
deriving instance Repr for Lean.QuotVal
deriving instance Repr for Lean.InductiveVal
deriving instance Repr for Lean.ConstructorVal
deriving instance Repr for Lean.RecursorRule
deriving instance Repr for Lean.RecursorVal
deriving instance Repr for Lean.ConstantInfo
deriving instance Repr for Lean.ConstMap

deriving instance Repr for Lean.Kernel.Diagnostics
deriving instance Repr for Lean.ModuleIdx

stub_repr EnvExtensionState
deriving instance Repr for Lean.CompactedRegion
deriving instance Repr for Lean.EffectiveImport
instance : Repr EnvExtensionEntry := ⟨fun _ _ => "<EnvExtensionEntry>"⟩
deriving instance Repr for Lean.ModuleData
-- deriving instance Repr for Lean.EnvironmentHeader
-- deriving instance Repr for Lean.Kernel.Environment

class TypeRepr.{u} (α : Type u) where
  typeRepr : Nat →  Format
export TypeRepr (typeRepr)
instance {α} [TypeName α] : TypeRepr α where
  typeRepr _ := f!"{TypeName.typeName α}"

instance {α} [TypeRepr α] : TypeRepr (Option α) where
  typeRepr p :=
    let r := f!"Option {typeRepr α max_prec}"
    if p > 0 then f!"({r})" else r

instance {α} [TypeRepr α] : TypeRepr (Array α) where
  typeRepr p :=
    let r := f!"Array {typeRepr α max_prec}"
    if p > 0 then f!"({r})" else r

instance {α} [TypeRepr α] : TypeRepr (NameMap α) where
  typeRepr p :=
    let r := f!"NameMap {typeRepr α max_prec}"
    if p > 0 then f!"({r})" else r

instance {α} [TypeRepr α] : Repr (Task α) := ⟨fun _ _ => f!"<Task[{typeRepr α 0}]>"⟩
instance {α} [TypeRepr α] : Repr (IO.Promise α) := ⟨fun _ _ => f!"<Promise[{typeRepr α 0}]>"⟩

stub_repr Environment -- TODO: improve
-- instance {α} [Repr α] : Repr (Task α) := ⟨fun t _ => f!"[Task ↦ {repr t.get}]"⟩
-- instance {α} [Repr α] : Repr (IO.Promise α) := ⟨fun t _ => f!"[Promise ↦ {repr t.result?}]"⟩
instance {α} [Repr α] : Repr (Thunk α) := ⟨fun t _ => f!"fun () => {repr t.get}]"⟩
-- deriving instance TypeName for AsyncConst
deriving instance TypeName for ConstantVal, ConstantInfo, Dynamic, Kernel.Environment, InfoTree
instance : TypeRepr EnvExtensionState := ⟨fun _ => f!"EnvExtensionState"⟩
-- deriving instance Repr for Lean.AsyncConstantInfo
-- deriving instance Repr for Lean.AsyncConst
deriving instance Repr for Lean.PrefixTreeNode
deriving instance Repr for Lean.NamePart
deriving instance Repr for Lean.PrefixTreeNode

universe u v
variable (α : Type u) (β : Type v) [Repr α] [Repr β] (cmp : α → α → Ordering)

deriving instance Repr for Lean.PrefixTree α β cmp
deriving instance Repr for Lean.NameTrie α
-- deriving instance Repr for Lean.AsyncConsts
-- deriving instance Repr for AsyncContext

deriving instance Repr for NonScalar
-- private instance : Repr Lean.RealizationContext := ⟨fun _ _ => "<RealizationContext>"⟩
-- deriving instance Repr for Lean.Environment
deriving instance Repr for Lean.MessageDataContext

deriving instance Repr for Lean.OpenDecl
deriving instance Repr for Lean.NamingContext
deriving instance Repr for Lean.TraceData
-- deriving instance Repr for Lean.PPContext
stub_repr PPContext
stub_repr Option PPContext → BaseIO Dynamic
stub_repr MetavarContext → Bool
deriving instance Repr for Lean.MessageData
deriving instance Repr for Lean.Meta.Diagnostics
deriving instance Repr for Lean.Meta.State

set_option trace.debug true



deriving instance Repr for Lean.FileMap
stub_repr IO.CancelToken
deriving instance Repr for Lean.Core.Context


  deriving instance Repr for Lean.NameGenerator
  deriving instance Repr for Lean.DeclNameGenerator
  deriving instance Repr for Lean.TraceElem
  deriving instance Repr for Lean.TraceState
  deriving instance Repr for Lean.Core.Cache
  deriving instance Repr for Lean.MessageSeverity
  deriving instance Repr for Lean.BaseMessage
  deriving instance Repr for Lean.Message
  deriving instance Repr for Lean.NameSet
  deriving instance Repr for Lean.MessageLog
  deriving instance Repr for Lean.Elab.CommandContextInfo
  deriving instance Repr for Lean.Elab.PartialContextInfo
  deriving instance Repr for Lean.Elab.InfoTree
  deriving instance Repr for Lean.Elab.InfoState
  deriving instance Repr for Lean.Language.SnapshotTask.ReportingRange
  section
  local instance {α} : Repr (Task α) := ⟨fun _ _ => "Task[*]"⟩
  deriving instance Repr for Lean.Language.SnapshotTask
  end

  instance {α} [TypeName α] : Repr (IO.Ref α) := ⟨fun _ _ => f!"<IO.Ref {TypeName.typeName α}"⟩
  instance {α} [TypeName α] : Repr (IO.Ref (Option α)) :=
    ⟨fun _ _ => f!"<IO.Ref (Option {TypeName.typeName α})"⟩

  deriving instance Repr for Lean.Language.Snapshot.Diagnostics
  deriving instance Repr for Lean.Language.Snapshot
  deriving instance Repr for Lean.Language.SnapshotTree
  deriving instance Repr for Lean.Core.State

  deriving instance Repr for Lean.Elab.Command.Scope
  deriving instance Repr for Lean.Elab.Command.State
  deriving instance Repr for Lean.Elab.MacroStackElem
  deriving instance Repr for Lean.Elab.MacroStack
  deriving instance Repr for Lean.Language.SyntaxGuarded
  section
  local instance {α} : Repr (IO.Promise α) := ⟨fun _ _ => "Promise[*]"⟩
  deriving instance Repr for Lean.Language.SnapshotBundle
  end
  deriving instance Repr for Lean.Language.DynamicSnapshot
  deriving instance Repr for Lean.Elab.Command.Context

  -- deriving instance Repr for Macro.State
  stub_repr Option (MVarId → Expr → Expr → MetaM MessageData)
  variable (γ : Type) [Repr γ] in
  deriving instance Repr for MVarIdMap γ
  stub_repr FixedTermElabRef
  deriving instance Repr for Lean.Elab.Term.SavedContext
  deriving instance Repr for Lean.Elab.Term.TacticMVarKind
  deriving instance Repr for Lean.Elab.Term.SyntheticMVarKind
  deriving instance Repr for Lean.Elab.Term.SyntheticMVarDecl
  deriving instance Repr for Lean.Elab.Term.MVarErrorKind
  deriving instance Repr for Lean.Elab.Term.MVarErrorInfo
  deriving instance Repr for Lean.Elab.Term.LevelMVarErrorInfo
  deriving instance Repr for Lean.AttributeKind
  deriving instance Repr for Lean.Elab.Attribute
  deriving instance Repr for Lean.Elab.TerminationBy
  deriving instance Repr for Lean.Elab.PartialFixpointType
  deriving instance Repr for Lean.Elab.PartialFixpoint
  deriving instance Repr for Lean.Elab.DecreasingBy
  deriving instance Repr for Lean.Elab.TerminationHints
  deriving instance Repr for Lean.Elab.Term.LetRecToLift
  deriving instance Repr for Lean.Elab.Term.State


  deriving instance Repr for Lean.Elab.AutoBoundImplicitContext
  stub_repr Name → Bool
  deriving instance Repr for Tactic.State
  deriving instance Repr for Core.SavedState
  deriving instance Repr for Meta.SavedState
  deriving instance Repr for Term.SavedState
  deriving instance Repr for Tactic.SavedState
  deriving instance Repr for Tactic.TacticFinishedSnapshot
  deriving instance Repr for Tactic.TacticParsedSnapshot
  deriving instance Repr for Lean.Elab.Term.Context


  deriving instance Repr for SyntheticMVarKind

-- run_cmd do
--   logInfo m!"{repr <|← get}"
