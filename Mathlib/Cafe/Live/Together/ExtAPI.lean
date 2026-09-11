module

public import Mathlib.Init
public import Lean
public import Qq
public meta import Mathlib.Init
public meta import Lean
import all Lean.ExtraModUses

open Lean

set_option autoImplicit false

public meta section

-- From Nate!
open Lean Elab Command in
elab tk:"#docstr " name:ident : command => do
  let env ← getEnv
  let ns ← liftCoreM (realizeGlobalConstNoOverloadWithInfo name)
  let some x ← findDocString? env ns | throwError "no docstring :("
  logInfoAt tk m!"{x}"

open Lean Meta Elab Tactic

namespace Mathlib.Tactic.GCongr

/-- An extension for `gcongr_forward`. -/
structure ForwardExt where
  eval (h : Expr) (goal : MVarId) : MetaM Unit
deriving TypeName

@[expose]
def Test := Nat → MetaM Unit

#eval applyDerivingHandlers `TypeName #[``Test]

#eval TypeName.typeName Test

@[gcongr_forward]
def xyz : Nat := 0

/--
info: @[reducible, expose] def Lean.ImportM : Type → Type :=
ReaderT ImportM.Context IO
-/
#guard_msgs in
#print ImportM

-- is there a command to show the docstring?
-- i have one! :)
/--
info: Like `evalConst`, but first check that `constName` indeed is a declaration of type `typeName`.
Note that this function cannot guarantee that `typeName` is in fact the name of the type `α`.
-/
#guard_msgs in
#docstr Environment.evalConstCheck --
/--
info: Evaluates the given declaration under the given environment to a value of the given type.
This function is only safe to use if the type matches the declaration's type in the environment
and if `enableInitializersExecution` has been used before importing any modules.

If `checkMeta` is true (the default), the function checks that all referenced imported constants are
marked or imported as `meta` or otherwise fails with an error. It should only be set to `false` in
cases where it is acceptable for code to work only in the language server, where more IR is loaded,
such as in `#eval`.
-/
#guard_msgs in
#docstr Environment.evalConst

variable (α : Type) [TypeName α]

/-- Read an arbitrary plugin to some tactic from a declaration. -/
def mkPlugin (n : Name) : ImportM α := do
  let { env, opts } ← read
  IO.ofExcept <| unsafe env.evalConstCheck α opts (TypeName.typeName α) n


#print ScopedEnvExtension
/--
error: unexpected type at 'Mathlib.Tactic.GCongr.xyz', `Mathlib.Tactic.GCongr.ForwardExt` expected
-/
#guard_msgs in
run_meta do (← mkPlugin ForwardExt ``xyz).eval default default

structure ScopedDeclEvalExtensionDescr (α : Type) [TypeName α] where
  mkInitial : IO (List (Name × α)) := pure []

@[expose]
def ScopedDeclEvalExtension (α /- ForwardExt -/) [TypeName α] :=
  ScopedEnvExtension Name (Name × α) (List (Name × α))
deriving Nonempty

#print Lean.Parser.Term.declName
#check `(decl_name%)

-- defined like this
-- open Lean Elab Term in
-- @[builtin_term_elab declName] meta def elabDeclName : TermElab := adaptExpander fun _ => do
--   let some declName ← getDeclName?
--     | throwError "invalid `decl_name%` macro, the declaration name is not available"
--   return (quote declName : Term)

theorem proofExample (x y : Nat) (h : x = y := by simp) : x + 1 = y + 1 := by rw [h]

/-- info: proofExample 20 (10 + 10) (of_eq_true (eq_self 20)) : 20 + 1 = 10 + 10 + 1 -/
#guard_msgs in #check proofExample 20 (10 + 10)

meta def registerScopedDeclEvalExtension {α} [TypeName α]
    (descr : ScopedDeclEvalExtensionDescr α) (declName : Name := by exact decl_name%) :
    IO (ScopedDeclEvalExtension α) := do
  registerScopedEnvExtension { descr with
    name := declName
    ofOLeanEntry _ pluginName := do pure (pluginName, ← mkPlugin α pluginName)
    -- List (Name × α) → Name → ImportM (Name × α)
    toOLeanEntry : Name × α → Name := fun (pluginName, _) => pluginName -- Name × α → Name
    addEntry := flip .cons -- List (Name × α) → Name × α → List (Name × α)
    -- finalizeImport := id
    -- TODO: export entries?
  }






#check Lean.Elab.syntaxNodeKindOfAttrParam
/--
info: def Lean.Elab.syntaxNodeKindOfAttrParam : Name → Syntax → AttrM SyntaxNodeKind :=
fun defaultParserNamespace stx => do
  let k ← Attribute.Builtin.getId stx
  checkSyntaxNodeKindAtCurrentNamespaces k <|>
      checkSyntaxNodeKind (defaultParserNamespace ++ k) <|>
        Lean.throwError (toMessageData "invalid syntax node kind `" ++ toMessageData k ++ toMessageData "`")
-/
#guard_msgs in
#print Lean.Elab.syntaxNodeKindOfAttrParam

/-- what this does -/
syntax (name := goncgr_forward) "gcongr_forward" term term : attr

#print ensureAttrDeclIsMeta

-- compilation succeeds!
def a : Nat := sorry

structure ScopedDeclEvalAttrDescr (α) [TypeName α]
    extends ScopedDeclEvalExtensionDescr α where
  attrName : Name
  attrDescr : String := s!"The `[{attrName}]` attribute"

#check recordIndirectModUse
#check recordExtraModUse

def registerScopedDeclEvalAttr {α} [TypeName α]
    (descr : ScopedDeclEvalAttrDescr α)
    (extName : Name := by exact decl_name%) :
    IO (ScopedDeclEvalExtension α) := do
  let ext ← registerScopedDeclEvalExtension descr.toScopedDeclEvalExtensionDescr extName
  registerBuiltinAttribute {
    name := descr.attrName
    descr := descr.attrDescr
    applicationTime := .afterCompilation
    add declName stx kind := do
      Attribute.Builtin.ensureNoArgs stx
      ensureAttrDeclIsMeta descr.attrName declName kind
      let env ← getEnv
      unless (env.getModuleIdxFor? declName).isNone do
        throwAttrDeclInImportedModule descr.attrName declName
      -- ignore in progress definitions
      if (IR.getSorryDep env declName).isSome then return
      let plugin ← mkPlugin α declName
      ext.add (declName, plugin) kind
    erase decl := do
      modifyEnv (fun env => ext.modifyState env fun state => state.filter (·.1 != decl))
  }
  return ext

#eval (3...10).iter.toArray

structure IterState (α : Type) where
  l : List (Name × α)

variable  {m : Type → Type} [Monad m] [MonadEnv m] [MonadTrace m] [MonadOptions m]
    [MonadRef m] [AddMessageContext m]

#print Std.IterStep
instance : Std.Iterator (IterState α) CoreM α where
  IsPlausibleStep _ _ := True
  step it := do
    let (name, plugin) :: rest := it.internalState.l
      | pure (.deflate ⟨.done, trivial⟩)
    recordExtraModUseFromDecl name (isMeta := true)
    pure (.deflate ⟨.yield { internalState := { l := rest }} plugin, trivial⟩)

instance : Std.IteratorLoop (IterState α) CoreM m := .defaultImplementation


def testIterM (l : List (Name × α)) : CoreM (Std.IterM (α := IterState α) CoreM α) :=
  return { internalState.l := l }

def useItNow : MetaM Unit := do
  let things := [(``Lean.versionString, Lean.versionString)]
  for x in ← testIterM String things do
    logInfo m!"{x}"

def ScopedDeclEvalExtension.iterM (ext : ScopedDeclEvalExtension α) : CoreM (Std.IterM (α := IterState α) CoreM α) :=
  return { internalState.l := ext.getState (← getEnv) }

meta def resetExtraModUses : Lean.CoreM Unit := do
  Lean.modifyEnv (Lean.PersistentEnvExtension.setState Lean.extraModUses · ⟨[], ∅⟩)
  Lean.modifyEnv (Lean.PersistentEnvExtension.setState Lean.isExtraRevModUseExt · ⟨[], ()⟩)

meta def _root_.Lean.ExtraModUse.toImport (e : ExtraModUse) : Import :=
  { e with }

meta def showExtraModUses : Lean.CoreM Unit := do
  Lean.logInfo m!"Entries: {toString <| (Lean.extraModUses.getEntries (← Lean.getEnv)).map (·.toImport)}\n\
    Is rev mod use: {!(Lean.isExtraRevModUseExt.getEntries (← Lean.getEnv)).isEmpty}"

#eval resetExtraModUses

/--
info: 4.34.0-rc2
---
info: ()
-/
#guard_msgs in
run_meta do
  logInfo m!"{← useItNow}"

/--
info: Entries: [import Lean.Message, import Init.Notation, meta import Init.Meta.Defs]
Is rev mod use: false
-/
#guard_msgs in
#eval showExtraModUses

initialize registerBuiltinAttribute {
  name := `goncgr_forward
  descr := "adds a gcongr_forward extension"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    Attribute.Builtin.ensureNoArgs stx
    unless kind == AttributeKind.global do
      throwAttrMustBeGlobal `gcongr_forward kind
    ensureAttrDeclIsMeta `gcongr_forward declName kind
    let env ← getEnv
    unless (env.getModuleIdxFor? declName).isNone do
      throwError "invalid attribute `[{descr.attrName}]`, declaration is in an imported module"
    if (IR.getSorryDep env declName).isSome then return -- ignore in progress definitions
    let ext ← mkPlugin ForwardExt declName
    setEnv <| forwardExt.addEntry env (declName, ext)
    recordExtraRevUseOfCurrentModule
}

end GCongr

end Mathlib.Tactic

open Mathlib.Tactic.GCongr

/--
info: @[reducible] def autoParam.{u} : Sort u → Syntax → Sort u :=
fun α tactic => α
-/
#guard_msgs in
#print autoParam
/--
info: meta def Mathlib.Tactic.GCongr.registerScopedDeclEvalExtension._auto_1 : Syntax :=
Syntax.node SourceInfo.none `Lean.Parser.Tactic.tacticSeq
  (#[].push
    (Syntax.node SourceInfo.none `Lean.Parser.Tactic.tacticSeq1Indented
      (#[].push
        (Syntax.node SourceInfo.none `null
          (#[].push
            (Syntax.node SourceInfo.none `Lean.Parser.Tactic.exact
              ((#[].push (mkAtom "exact")).push
                (Syntax.node SourceInfo.none `Lean.Parser.Term.declName (#[].push (mkAtom "decl_name%"))))))))))
-/
#guard_msgs in
#print registerScopedDeclEvalExtension._auto_1
/--
info: meta def Mathlib.Tactic.GCongr.registerScopedDeclEvalExtension : {α : Type} →
  [inst : TypeName α] →
    ScopedDeclEvalExtensionDescr α →
      autoParam Name registerScopedDeclEvalExtension._auto_1 → IO (ScopedDeclEvalExtension α)
-/
#guard_msgs in
#print sig registerScopedDeclEvalExtension

open Lean Elab Command
instance : Repr Options where
  reprPrec _ _ := "<Options>"

open Qq in
instance : ToExpr Options where
  toExpr _ := q(({} : Options))
  toTypeExpr := q(Options)

open Qq in
instance : ToExpr Syntax where
  toExpr _ := q(Syntax.missing)
  toTypeExpr := q(Syntax)

deriving instance ToExpr for SyntaxNodeKinds
-- deriving instance ToExpr for SourceInfo
-- deriving instance ToExpr for Syntax
deriving instance ToExpr for TSyntax
deriving instance ToExpr for OpenDecl
deriving instance ToExpr for Scope -- hello! :)


/-
Task:
- create extension that evaluates meta declarations
- create discrimination tree extension?
- create attribute along with it

- API for evaluating meta declarations
-/

/--
info: inductive Lean.ScopedEnvExtension.Entry : Type → Type
number of parameters: 1
constructors:
Lean.ScopedEnvExtension.Entry.global : {α : Type} → α → ScopedEnvExtension.Entry α
Lean.ScopedEnvExtension.Entry.scoped : {α : Type} → Name → α → ScopedEnvExtension.Entry α
-/
#guard_msgs in
#print ScopedEnvExtension.Entry
/--
info: Lean.ScopedEnvExtension.ext {α β σ : Type} (self : ScopedEnvExtension α β σ) :
  PersistentEnvExtension (ScopedEnvExtension.Entry α) (ScopedEnvExtension.Entry β) (ScopedEnvExtension.StateStack α β σ)
-/
#guard_msgs in #check ScopedEnvExtension.ext

/--
info: def Lean.ScopedEnvExtension.addCore : {α β σ : Type} →
  Environment → ScopedEnvExtension α β σ → β → AttributeKind → Name → Environment :=
fun {α β σ} env ext b kind namespaceName =>
  match kind with
  | AttributeKind.global => ext.addEntry env b
  | AttributeKind.local => ext.addLocalEntry env b
  | AttributeKind.scoped => ext.addScopedEntry env namespaceName b
-/
#guard_msgs in
#print ScopedEnvExtension.addCore


/--
info: structure Lean.ScopedEnvExtension.ScopedEntries (β : Type) : Type
number of parameters: 1
fields:
  Lean.ScopedEnvExtension.ScopedEntries.map : SMap Name (PArray β) :=
    { }
constructor:
  Lean.ScopedEnvExtension.ScopedEntries.mk {β : Type} (map : SMap Name (PArray β)) : ScopedEnvExtension.ScopedEntries β
-/
#guard_msgs in
#print ScopedEnvExtension.ScopedEntries

/--
info: structure Lean.ScopedEnvExtension.StateStack (α β σ : Type) : Type
number of parameters: 3
fields:
  Lean.ScopedEnvExtension.StateStack.stateStack : List (ScopedEnvExtension.State σ) :=
    ∅
  Lean.ScopedEnvExtension.StateStack.scopedEntries : ScopedEnvExtension.ScopedEntries β :=
    { }
  Lean.ScopedEnvExtension.StateStack.newEntries : List (ScopedEnvExtension.Entry α) :=
    []
constructor:
  Lean.ScopedEnvExtension.StateStack.mk {α β σ : Type} (stateStack : List (ScopedEnvExtension.State σ))
    (scopedEntries : ScopedEnvExtension.ScopedEntries β) (newEntries : List (ScopedEnvExtension.Entry α)) :
    ScopedEnvExtension.StateStack α β σ
-/
#guard_msgs in
#print ScopedEnvExtension.StateStack

/-(TypeName.typeName α) - Environment extensions for `gcongrForward` declarations -/
initialize forwardExt : ScopedDeclEvalExtension ForwardExt ←
  registerScopedDeclEvalAttr {
    attrName := `gcongr_forward




/---

ad: https://github.com/leanprover/lean4/issues/15081

FREE AD SPACE: YOUR AD HERE
-/






}
