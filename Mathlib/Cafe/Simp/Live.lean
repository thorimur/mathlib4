module

public meta import Lean
public import Lean
public import Mathlib.Tactic.SudoSetOption
import all Lean.Meta.Tactic.Simp.Types
import all Lean.Meta.Tactic.Simp.SimpTheorems
public import Qq
example : True := by
  simp

open Lean Meta Elab Tactic

/-
  "simp" optConfig (discharger)? (" only")? (" [" ((simpStar <|> simpErase <|> simpLemma),*,?) "]")?
  (location)?
-/
@[builtin_tactic Lean.Parser.Tactic.simp] def evalSimp : Tactic := fun stx => withMainContext do withSimpDiagnostics do
  let r@{ ctx, simprocs, dischargeWrapper, simpArgs } ← mkSimpContext stx (eraseLocal := false)
  if ctx.config.suggestions then
    throwError "+suggestions requires using simp? instead of simp"
  let stats ← dischargeWrapper.with fun discharge? =>
    withLoopChecking r do
      simpLocation ctx simprocs discharge? (expandOptLocation stx[5])
  if tactic.simp.trace.get (← getOptions) then
    traceSimpCall stx stats.usedTheorems
  else if Linter.getLinterValue linter.unusedSimpArgs (← Linter.getLinterOptions) then
    withRef stx do
      warnUnusedSimpArgs simpArgs stats.usedTheorems
  return stats.diag

#check evalSimp
#print Simp.Context --here you are
#check Simp.Context

#check mkSimpContext -- For elaborating syntax to a context! Not typically used
#print MkSimpContextResult


/--
info: Lean.Meta.Simp.mkContext (config : Simp.Config := { }) (simpTheorems : SimpTheoremsArray := ∅)
  (congrTheorems : SimpCongrTheorems := { }) (userConfig : Options := ∅) : MetaM Simp.Context
-/
#guard_msgs in
#check Simp.mkContext -- entry point for simp context construction in meta code

-- Array of simp *sets*
-- abbrev SimpTheoremsArray := Array SimpTheorems

/--
info: Lean.Meta.SimpTheoremsArray.addTheorem (thmsArray : SimpTheoremsArray) (id : Origin) (h : Expr)
  (config : ConfigWithKey := simpGlobalConfig) : MetaM SimpTheoremsArray
-/
#guard_msgs in
#check SimpTheoremsArray.addTheorem -- adds to the first simp set!

def f := true

/--
info: @[backward_defeq] private theorem f.eq_1 : f = true :=
Eq.refl f
-/
#guard_msgs in
#print f.eq_1

def P : Prop := True

@[simp]
theorem P_true : P := trivial

-- ==>

/--
info: private theorem P_true._simp_1 : P = True :=
eq_true P_true
-/
#guard_msgs in #print P_true._simp_1

example : True := by simp [f] -- turns into simp [f.eq_1]

#check Lean.Meta.SimpTheorems.addDeclToUnfold
#check Lean.Meta.addDeclToUnfold

#check mkSimpTheoremFromConst
recall SimpTheorems.addConst (s : SimpTheorems) (declName : Name) (post := true) (inv := false) (prio : Nat := eval_prio default) : MetaM SimpTheorems := do
  let simpThms ← mkSimpTheoremFromConst declName post inv prio
  return simpThms.foldl SimpTheorems.addSimpTheorem s

/-
/--
The theorems in a simp set.
-/
structure SimpTheorems where
  pre          : SimpTheoremTree := DiscrTree.empty
  post         : SimpTheoremTree := DiscrTree.empty
  lemmaNames   : PHashSet Origin := {}
  /--
  Constants (and let-declaration `FVarId`) to unfold.
  When `zetaDelta := false`, the simplifier will expand a let-declaration if it is in this set.
  -/
  toUnfold     : PHashSet Name := {}
  erased       : PHashSet Origin := {}
  toUnfoldThms : PHashMap Name (Array Name) := {}
  deriving Inhabited
-/

example : True := by simp [← trivial]



/--
info: @[reducible, expose] def Lean.Meta.SimpTheoremTree : Type :=
DiscrTree SimpTheorem
-/
#guard_msgs in
#print SimpTheoremTree

/-- info: Lean.Expr.const (declName : Name) (us : List Level) : Expr -/
#guard_msgs in
#check Expr.const

/--
  The fields `levelParams` and `proof` are used to encode the proof of the simp theorem.
  If the `proof` is a global declaration `c`, we store `Expr.const c []` at `proof` without the universe levels, and `levelParams` is set to `#[]`
  When using the lemma, we create fresh universe metavariables.
  Motivation: most simp theorems are global declarations, and this approach is faster and saves memory.

  The field `levelParams` is not empty only when we elaborate an expression provided by the user, and it contains universe metavariables.
  Then, we use `abstractMVars` to abstract the universe metavariables and create new fresh universe parameters that are stored at the field `levelParams`.
-/
structure SimpTheorem where
  keys        : Array SimpTheoremKey := #[]
  /--
    It stores universe parameter names for universe polymorphic proofs.
    Recall that it is non-empty only when we elaborate an expression provided by the user.
    When `proof` is just a constant, we can use the universe parameter names stored in the declaration.
   -/
  levelParams : Array Name := #[]
  proof       : Expr -- if you want to read the proof, use `getValue` instead
  priority    : Nat  := eval_prio default
  post        : Bool := true
  /-- `perm` is true if lhs and rhs are identical modulo permutation of variables. -/
  perm        : Bool := false -- for something like `add_comm`
  /--
    `origin` is mainly relevant for producing trace messages.
    It is also viewed an `id` used to "erase" `simp` theorems from `SimpTheorems`.
  -/
  origin      : Origin
  /--
  `rfl` is true if `proof` is by `Eq.refl`, `rfl` or a `@[defeq]` theorem.
  -/
  rfl         : Bool
  /--
  `backwardRfl` is true if `proof` is by a `@[backward_defeq]` theorem (i.e. rfl at default,
  but not instance, transparency). Honored by `dsimp` only when
  `backward.defeqAttrib.useBackward` is set.
  -/
  backwardRfl : Bool := false
  deriving Inhabited



/--
info: Lean.Meta.SimpTheorems.addConst (s : SimpTheorems) (declName : Name) (post : Bool := true) (inv : Bool := false)
  (prio : Nat := 1000) : MetaM SimpTheorems
-/
#guard_msgs in
#check SimpTheorems.addConst

/--
info: Lean.Meta.SimpTheorems.addDeclToUnfold (d : SimpTheorems) (declName : Name) : MetaM SimpTheorems
-/
#guard_msgs in #check SimpTheorems.addDeclToUnfold

#check unfold

#check getSimpTheorems
#check getSimpCongrTheorems
#check Simp.mkContext {}

/-
  let mut simpTheorems ← if simpOnly then
    simpOnlyBuiltins.foldlM (·.addConst ·) ({} : SimpTheorems) -- iff_self, eq_self
  else
    simpTheorems
-/

def getSimpOnlyTheorems : MetaM Meta.SimpTheorems := do -- `MetaM` instead of `CoreM`, interestingly
  Elab.Tactic.simpOnlyBuiltins.foldlM (·.addConst ·) {}

/-- info: [`eq_self, `iff_self] -/
#guard_msgs in
#eval Elab.Tactic.simpOnlyBuiltins

/--
info: Lean.Meta.simpGoal
  (mvarId : MVarId)
  (ctx : Simp.Context)
  (simprocs : Simp.SimprocsArray := #[])
  (discharge? : Option Simp.Discharge := none)
  (simplifyTarget : Bool := true)
  (fvarIdsToSimp : Array FVarId := #[])
  (stats : Simp.Stats := { }) :
  MetaM (Option (Array FVarId × MVarId) × Simp.Stats)
-/
#guard_msgs (whitespace := lax) in
#check Lean.Meta.simpGoal

-- Related
#check dsimpGoal
#check simpTarget -- just the goal, not its local decls
#check simpLocalDecl
#check simpIfLocalDecl -- red herring! Related to `if-then-else` simplification
#check simpTargetStar
#check simpAll -- for `simp_all`

/--
info: Lean.Meta.simp
  (e : Expr)
  (ctx : Simp.Context)
  (simprocs : Simp.SimprocsArray := #[])
  (discharge? : Option Simp.Discharge := none)
  (stats : Simp.Stats := { }) :
  MetaM (Simp.Result × Simp.Stats)
-/
#guard_msgs (whitespace := lax) in
#check simp

#print Simp.Result
#check Qq.

#print Simp.ResultQ
/--
info: def Lean.Meta.Simp.ResultQ.mk : {u : Level} →
  {α : Q(Sort u)} → {e : Q(«$α»)} → (expr : Q(«$α»)) → Option Q(«$e» = «$expr») → optParam Bool true → Simp.ResultQ e :=
<not imported>
-/
#guard_msgs in
#print Simp.ResultQ.mk



/-- The result of simplifying some expression `e`. -/
structure Simp.Result where
  /-- The simplified version of `e` -/
  expr           : Expr
  /-- A proof that `$e = $expr`, where the simplified expression is on the RHS.
  If `none`, the proof is assumed to be `refl`. -/
  proof?         : Option Expr := none
  /--
  If `cache := true` the result is cached.
  Warning: we will remove this field in the future. It is currently used by
  `arith := true`, but we can now refactor the code to avoid the hack.
  -/
  cache          : Bool := true


  -- Various bits of API for manipulating `Simp.Result`s and constructing new transformation/chaining proofs:
#check Simp.mkCongr -- not sure why these aren't in `Simp.Result`
#check Simp.mkCongrArg
#check Simp.mkCongrFun
#check Simp.Result.mkEqSymm
#check Simp.Result.mkEqTrans
#check Simp.Result.mkCast
#check Simp.Result.mkEqMP
#check Simp.Result.mkEqMPR

-- We can then apply those `Simp.Result`s to various things:
#check applySimpResult
#check applySimpResultToFVarId
-- ^transforms a type
-- ^takes in an `MVarId` but usually does not assign it.
-- ^returns `Option (Expr × Expr)`, where `val` is essentially the proof

def applySimpResult (mvarId : MVarId) (val : Expr) (type : Expr) (r : Simp.Result) (mayCloseGoal := true) : MetaM (Option (Expr × Expr)) := do
  if mayCloseGoal && r.expr.isFalse then
    match r.proof? with
    | some eqProof => mvarId.assign (← mkFalseElim (← mvarId.getType) (mkApp4 (mkConst ``Eq.mp [Level.zero]) type r.expr eqProof val))
    | none => mvarId.assign (← mkFalseElim (← mvarId.getType) val)
    return none
  else
    match r.proof? with
    | some eqProof =>
      let u ← getLevel type
      return some (mkApp4 (mkConst ``Eq.mp [u]) type r.expr eqProof val, r.expr)
    | none =>
      if r.expr != type then
        return some ((← mkExpectedTypeHint val r.expr), r.expr)
      else
        return some (val, r.expr)

-- the following use that under the hood and modify the goal appropriately:
#check applySimpResultToLocalDecl
#check applySimpResultToTarget -- does not "apply" the simp result using the above!

/--
info: @[reducible, expose] def Lean.Meta.Simp.Simproc : Type :=
Expr → SimpM Simp.Step
-/
#guard_msgs in
#print Simp.Simproc
#print Simp.Step
#print TransformStep
#print Simp.Methods
#print Simp.Context

#check mkSimpContext
#print MkSimpContextResult
#print simp -- also takes in SimprocsArray

#check Simp.preDefault

opaque tryNormNum (post := false) : Simp.Simproc := fun _ => pure default
/-- A `Methods` implementation which calls `norm_num`. -/
def methods (simprocs : Simp.SimprocsArray := #[]) (useSimp := true) : Simp.Methods :=
  if useSimp then {
    pre := Simp.preDefault simprocs >> tryNormNum
    post := Simp.postDefault simprocs >> tryNormNum (post := true)
    discharge? := Simp.dischargeGround
  } else {
    pre := tryNormNum
    post := tryNormNum (post := true)
    discharge? := Simp.dischargeGround
  }


/--
info: def Lean.Meta.Simp.andThen : Simp.Simproc → Simp.Simproc → Simp.Simproc :=
fun f g e => do
  let __do_lift ← f e
  match __do_lift with
    | Simp.Step.done r => pure (Simp.Step.done r)
    | Simp.Step.continue => g e
    | Simp.Step.continue (some r) => do
      let __do_lift ← g r.expr
      liftM (Simp.mkEqTransResultStep r __do_lift)
    | Simp.Step.visit r => pure (Simp.Step.visit r)
-/
#guard_msgs in
#print Simp.andThen
#synth AndThen Simp.Simproc

#print Simp.instAndThenSimproc

/--
info: @[reducible, expose] def Lean.Meta.Simp.SimpM : Type → Type :=
ReaderT Simp.MethodsRef (ReaderT Simp.Context (StateRefT' IO.RealWorld Simp.State MetaM))
-/
#guard_msgs in -- Simp.MethodsRef ≈ Simp.Methods (forward declaration)
#print SimpM
#print Simp.State
-- Maybe we should have one with similar arguments to `simpGoal`!
-- I.e. both FVarIds and MVarId

#check Simp.Stats
#check Lean.Elab.Tactic.simpLocation

#check Simp.getSimprocs

structure UsedSimps where
  -- We should use `PHashMap` because we backtrack the contents of `UsedSimps`
  -- The natural number tracks the insertion order
  map  : PHashMap Origin Nat := {}
  size : Nat := 0
  deriving Inhabited

structure Diagnostics where
  /-- Number of times each simp theorem has been used/applied. -/
  usedThmCounter : PHashMap Origin Nat := {}
  /-- Number of times each simp theorem has been tried. -/
  triedThmCounter : PHashMap Origin Nat := {}
  /-- Number of times each congr theorem has been tried. -/
  congrThmCounter : PHashMap Name Nat := {}
  /--
  When using `Simp.Config.index := false`, and `set_option diagnostics true`,
  for every theorem used by `simp`, we check whether the theorem would be
  also applied if `index := true`, and we store it here if it would not have
  been tried.
  -/
  thmsWithBadKeys : PArray SimpTheorem := {}
  deriving Inhabited

structure Stats where
  usedTheorems : UsedSimps := {}
  diag : Diagnostics := {}
  deriving Inhabited

#check simpGoal


-- #check

example : 3 ∣ 9 := by
  simp only [← Nat.reduceDvd]


-- Low level: `Simp.main`
-- Reading `Sym.Simp` makes things clearer

#print Lean.Parser.Term.set_option
#print Parser.Command.optionValue

macro tk:"set_option! " id:ident val:optionValue : command =>
  if val.raw.isAtom then
    match val.raw.getAtomVal with
    | "true" => `(sudo%$tk set_option%$tk $id $(mkIdent `true))
    | "false" => `(sudo%$tk set_option%$tk $id $(mkIdent `false))
    | _ => Macro.throwUnsupported
  else
    match val with
    | `(optionValue| $n:num) => `(sudo%$tk set_option%$tk $id $n:num)
    | `(optionValue| $s:str) => `(sudo%$tk set_option%$tk $id $s:str)
    | _ => Macro.throwUnsupported

set_option! trace.foo true


elab "foo" ("!")? : command => do pure ()
elab "bar!" : command => do pure ()

macro tk:"foo!" : command => `(foo%$tk !%$tk)

foo
foo!
bar!

run_cmd
  trace[«foo»] "hi"
  -- logInfo m!"{← getBoolOption `foo}"


-- set_option doc.verso true in
-- /-- `'a'` -/
-- def tmp := 2
