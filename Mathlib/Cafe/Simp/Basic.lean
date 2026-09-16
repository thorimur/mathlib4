module

public meta import Lean
public import Lean

/- Elaborator for syntax (not typically called): -/
#check Lean.Elab.Tactic.evalSimp

open Lean Meta

#check Lean.Elab.Tactic.simpLocation

-- **Main entry point**, when simplifying a goal and/or its local decls:
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

-- But most illustratively, let's look at
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

-- This takes in a bare expression and returns a `Simp.Result`.

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

/- This pattern is very useful! When you write a tactic which transforms expressions, you need to create both the normalized expression, and build the proof that lets you show it's equal to the original one. -/

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
-- ^transforms a type
-- ^takes in an `MVarId` but usually does not assign it.
-- ^returns `Option (Expr × Expr)`, where `val` is essentially the proof

-- the following use that under the hood and modify the goal appropriately:
#check applySimpResultToFVarId
#check applySimpResultToLocalDecl
#check applySimpResultToTarget
-- Maybe we should have one with similar arguments to `simpGoal`!
-- I.e. both FVarIds and MVarId

-- And constructing this `Simp.Result` we have
#check simp

/-
The actual simp theorems are provided entirely through the `Simp.Context`.
It's the construction of this context from the environment that grabs the simp extension entries and actually provides them for use in `simp`.

This also holds the config and its settings.
-/
#check Simp.Context

/- It has a private constructor, so you have to make it. -/
/- From syntax, that's included in the result of `mkSimpContext`. We'll come back to this in more depth. -/
#check Elab.Tactic.mkSimpContext
/- The context used for `simp only` is constructed by `mkSimpOnly`, which you can then add to. -/
#check Elab.Tactic.mkSimpOnly
-- In `mkSimpContext`:
/-
  let mut simpTheorems ← if simpOnly then
    simpOnlyBuiltins.foldlM (·.addConst ·) ({} : SimpTheorems)
  else
    simpTheorems
-/
-- Q: What syntax does it actually want?

/- On the meta level, we can use `Simp.mkContext`, which takes in the non-internal data directly. -/
#check Simp.mkContext

/- Notice the following fields: -/
/-
  simpTheorems      : SimpTheoremsArray := {}
  congrTheorems     : SimpCongrTheorems := {}
-/

#check SimpTheoremsArray

/-
A `SimpTheoremsArray` is a collection of `SimpTheorems`. The first entry is the default simp set
and possible extensions as simp args (`simp [thm]`), further entries are custom simp sets added
a s simp arguments (`simp [my_simp_set]`). The array is scanned linear during rewriting.
This avoids the need for efficiently merging the `SimpTheorems` data structure.
-/
-- abbrev SimpTheoremsArray := Array SimpTheorems

-- The following lets you add a single theorem (`h`) to the (first) simp set in the `SimpTheoremsArray`.
/--
info: Lean.Meta.SimpTheoremsArray.addTheorem
  (thmsArray : SimpTheoremsArray)
  (id : Origin) (h : Expr)
  (config : ConfigWithKey := simpGlobalConfig) : MetaM SimpTheoremsArray
-/
#guard_msgs (whitespace := lax) in
#check SimpTheoremsArray.addTheorem

/- Since `Simp.Context` has a private constructor, use `Simp.Context.setSimpTheorems` to set it. -/
#check Simp.Context.setSimpTheorems

/- You may want to check if the simp theorem is erased first. This information is stored separately. (Or, perhaps, you want to erase it, with `SimpTheoremsArray.eraseTheorem` )-/
#check SimpTheoremsArray.isErased

/- We'll come back to `Origin`s, but for now just think of them as identifiers for simp lemmas with extra information about where they came from. Let's look at each of these: -/
#check SimpTheorems

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

/- We likewise have -/
#check SimpTheorems.addSimpTheorem

/- Getting closer! Digging further: -/
abbrev SimpTheoremTree := DiscrTree SimpTheorem

/- And finally, we have each: -/
#check SimpTheorem

/--
  The fields `levelParams` and `proof` are used to encode the proof of the simp theorem.
  If the `proof` is a global declaration `c`, we store `Expr.const c []` at `proof` without the universe levels, and `levelParams` is set to `#[]`
  When using the lemma, we create fresh universe metavariables.
  Motivation: most simp theorems are global declarations, and this approach is faster and saves memory.

  The field `levelParams` is not empty only when we elaborate an expression provided by the user, and it contains universe metavariables.
  Then, we use `abstractMVars` to abstract the universe metavariables and create new fresh universe parameters that are stored at the field `levelParams`.
-/
structure SimpTheorem where
  keys        : Array SimpTheoremKey := #[] -- `abbrev SimpTheoremKey := DiscrTree.Key`
  /--
    It stores universe parameter names for universe polymorphic proofs.
    Recall that it is non-empty only when we elaborate an expression provided by the user.
    When `proof` is just a constant, we can use the universe parameter names stored in the declaration.
   -/
  levelParams : Array Name := #[]
  proof       : Expr
  priority    : Nat  := eval_prio default
  post        : Bool := true
  /-- `perm` is true if lhs and rhs are identical modulo permutation of variables. -/
  perm        : Bool := false
  /--
    `origin` is mainly relevant for producing trace messages.
    It is also viewed an `id` used to "erase" `simp` theorems from `SimpTheorems`.
  -/
  origin      : Origin
  /--
  `rfl` is true if `proof` is by `Eq.refl`, `rfl` or a `@[defeq]` theorem.
  -/
  rfl         : Bool -- Relevant to `dsimp`
  /--
  `backwardRfl` is true if `proof` is by a `@[backward_defeq]` theorem (i.e. rfl at default,
  but not instance, transparency). Honored by `dsimp` only when
  `backward.defeqAttrib.useBackward` is set.
  -/
  backwardRfl : Bool := false

/- So each simp set is essentially a discrtree of simp lemmas, where with each simp lemma we record some extra info. -/

/- Going back to `isErased`, for example, we see it takes in an `Origin`. We see each simp lemma is stored with an `Origin`. But what is `Origin`? -/
/--
An `Origin` is an identifier for simp theorems which indicates roughly
what action the user took which lead to this theorem existing in the simp set.
-/
inductive Origin where
  /-- A global declaration in the environment. -/
  -- NOTE: `inv` is `←`
  | decl (declName : Name) (post := true) (inv := false)
  /--
  A local hypothesis.
  When `contextual := true` is enabled, this fvar may exist in an extension
  of the current local context; it will not be used for rewriting by simp once
  it is out of scope but it may end up in the `usedSimps` trace.
  -/
  | fvar (fvarId : FVarId)
  /--
  A proof term provided directly to a call to `simp [ref, ...]` where `ref`
  is the provided simp argument (of kind `Parser.Tactic.simpLemma`).
  The `id` is a unique identifier for the call.
  -/
  | stx (id : Name) (ref : Syntax)
  /--
  Some other origin. `name` should not collide with the other types
  for erasure to work correctly, and simp trace will ignore this lemma.
  The other origins should be preferred if possible.
  -/
  | other (name : Name)

/- The `Origin` does not *just* function as an indication of where it came from; it's also the "key" for the `simp` theorem, and carries information about how it's used. -/

/- Look at: -/
-- `| decl (declName : Name) (post := true) (inv := false)`
/-
`inv` is `←`; `post` is the *absence* of `↓` (effectively `↑`, but we don't write that; things are `post` by default).

Now let's understand a bit about how simp actually simplifies. It traverses subexpressions, starting from the outermost expression. This is the `pre` (`↓`) direction. as it examines subsequent subexpressions, it applies `pre` (`↓`) lemmas and simprocs. Once it reaches the bottom, it now ascends back to the top and applies `post` (`↑`) along the way. This is the default.

Questions:
- Does it "restart" and go back in (`↓`) after post lemmas?
- Why does `add_assoc` work and not loop forever?
-/

/- We also have -/
/--
info: Lean.Meta.SimpTheorems.addConst
  (s : Meta.SimpTheorems)
  (declName : Name)
  (post : Bool := true) (inv : Bool := false)
  (prio : Nat := 1000) : MetaM Meta.SimpTheorems
-/
#guard_msgs (whitespace := lax) in
#check SimpTheorems.addConst

-- which uses
#check mkSimpTheoremFromConst
-- and fills in all the fields appropriately, as well as splitting into multiple theorems if necessary

-- related:
#check SimpTheorems.addDeclToUnfold
#check SimpTheorems.addLetDeclToUnfold
#check SimpTheorems.addSimpEntry
#check SimpTheorems.addSimpTheorem
#check SimpTheorems.add
-- all in `Lean.Meta.Tactic.Simp.SimpTheorems`

-- We can get the simp theorems with `getSimpTheorems`.
#check getSimpTheorems -- All `@[simp]` theorems, as usual
#check getSimpCongrTheorems -- Should supply this in general, even with `only`
-- Does this exist?
def getSimpOnlyTheorems : MetaM Meta.SimpTheorems := do -- `MetaM` instead of `CoreM`, interestingly
  Elab.Tactic.simpOnlyBuiltins.foldlM (·.addConst ·) {}

-- See `Elab.Tactic.mkSimpContext`, called by `evalSimp`, for defaults
#check Elab.Tactic.mkSimpContext

/-
Speaking, of, `SimpCongrTheorems`:
-/

/-
/--
  Data for user-defined theorems marked with the `congr` attribute.

  This type should be confused with `CongrTheorem` which represents different kinds of automatically
  generated congruence theorems. The `simp` tactic also uses some of them.
-/
structure SimpCongrTheorem where
  theoremName   : Name
  funName       : Name
  hypothesesPos : Array Nat
  priority      : Nat
deriving Inhabited, Repr

structure SimpCongrTheorems where
  lemmas : SMap Name (List SimpCongrTheorem) := {}
  deriving Inhabited, Repr
-/

open Elab Tactic

/-
The context-makers need a config.
Note: `elabSimpConfig` exists; can also use `{}` primarily, but also `neutralConfig` (not the default)
-/
#check elabSimpConfig

-- see also `Mathlib.Lean.Meta.Simp` for some more helpers

/- Certain `pp*` defs are useful for debugging and necessary due to monadic requirements, apparently. -/
#check ppOrigin -- does not actually need to be monadic (anymore?)
#check ppSimpTheorem -- likewise

meta def ppOrigin' {m} [Monad m] [MonadEnv m] : Meta.Origin → m MessageData
  | .decl n post inv => do
    let r := MessageData.ofConstName n
    match post, inv with
    | true,  true  => return m!"← {r}"
    | true,  false => return r
    | false, true  => return m!"↓ ← {r}"
    | false, false => return m!"↓ {r}"
  | .fvar n => return mkFVar n
  | .stx _ ref => return ref
  | .other n => return n

instance : ToMessageData Meta.Origin where
  toMessageData
    | .decl n post inv =>
      let r := .ofConstName n
      match post, inv with
      | true,  true  => m!"← {r}"
      | true,  false => r
      | false, true  => m!"↓ ← {r}"
      | false, false => m!"↓ {r}"
    | .fvar n => mkFVar n
    | .stx _ ref => ref
    | .other n => n

instance : ToMessageData Meta.SimpTheorem where
  toMessageData s :=
    m!"{s.origin}:{s.priority}{if s.perm then ":perm" else ""}\
      {if s.rfl then ":rfl" else ""}{if s.proof.isConst then m!"" else m!" := {s.proof}"}"

instance : ToMessageData Meta.SimpTheoremTree where
  toMessageData s := m!"{s.values}"


-- instance : ToMessageData Simp.Config where
--   toMessageData cfg :=

def toStructureMessage (s : Array (String × MessageData)) :=
  let s := s.map fun (s, m) => indentD m!"{s} := {.nestD m}"
  "{" ++ m!"".joinSep s.toList ++ "\n}"

instance : ToMessageData Meta.SimpTheorems where
  toMessageData thms := Id.run do
    let mut fields := #[
      ("pre", toMessageData thms.pre),
      ("post", toMessageData thms.post),
      ("lemmaNames", toMessageData thms.lemmaNames.toList)
    ]
    unless thms.toUnfold.isEmpty do
      fields := fields.push
        ("toUnfold", toMessageData (thms.toUnfold.toList.map MessageData.ofConstName))
    unless thms.erased.isEmpty do
      fields := fields.push
        ("erased", toMessageData thms.erased.toList)
    toStructureMessage fields

instance : ToMessageData Simp.Context where
  toMessageData ctx :=
    m!"{ctx.simpTheorems}"

run_meta
  let ctx ← Simp.mkContext
  logInfo m!"{ctx}"

-- run_meta
--   let ctx ← Simp.mkContext (simpTheorems := #[← getSimpTheorems])
--   logInfo m!"{ctx}"

/-
# Simprocs

- `simpGoal` takes in a `SimprocsArray`!
- This is returned along with (separately from) the `Simp.Context` in `mkSimpContext`:
  ```
  let simprocs ← if simpOnly then pure {} else Simp.getSimprocs
  ```
- ^ But we can also get them directly via `Simp.getSimprocs`

Overall the structure of things is similar:
-/

#check Simp.SimprocsArray -- abbrev SimprocsArray := Array Simprocs
#check Meta.Simprocs
/-
structure Simprocs where
  pre          : SimprocTree   := DiscrTree.empty
  post         : SimprocTree   := DiscrTree.empty
  simprocNames : PHashSet Name := {}
  erased       : PHashSet Name := {}
  deriving Inhabited
-/

#check Simp.SimprocTree -- abbrev SimprocTree := DiscrTree SimprocEntry
#check Simp.SimprocEntry
/-
/--
`Simproc` .olean entry.
-/
structure SimprocOLeanEntry where
  /-- Name of a declaration stored in the environment which has type `Simproc`. -/
  declName : Name
  post     : Bool := true
  keys     : Array SimpTheoremKey := #[]
  deriving Inhabited

/--
`Simproc` entry. It is the .olean entry plus the actual function.
-/
structure SimprocEntry extends SimprocOLeanEntry where
  /--
  Recall that we cannot store `Simproc` into .olean files because it is a closure.
  Given `SimprocOLeanEntry.declName`, we convert it into a `Simproc` by using the unsafe function `evalConstCheck`.
  -/
  proc : Sum Simproc DSimproc
-/

-- To get the standard simprocs
#check Simp.getSimprocs

-- To add/erase (takes in simproc declaration names)
#check Simp.Simprocs.add
#check Simp.Simprocs.erase
#check Simp.SimprocsArray.add
#check Simp.SimprocsArray.erase

/-
Internals:
`simpGoal` combines simprocs with the `Simp.Discharge := Expr → SimpM (Option Expr)` via:
-/
#check Simp.mkMethods
#check Simp.mkDefaultMethods

#check mkSimpContext

#check evalSimp

#check simpGoal

#check Simp.Discharge

/-
Note about `mkSimpContext`: actually returns much more:
```
structure MkSimpContextResult where
  ctx              : Simp.Context
  simprocs         : Simp.SimprocsArray
  dischargeWrapper : Simp.DischargeWrapper
  /-- The elaborated simp arguments with syntax -/
  simpArgs         : Array (Syntax × ElabSimpArgResult) := #[]
```
So we see that
-/


#check SimpM
/-
`SimpM` is `MetaM` together with:
- `Simp.Context` (simp theorems, etc.)
- `Simp.State`, caches + records (`UsedSimps`)
- `Simp.MethodsRef` holding `Simp.Methods`, which holds pre/post (d)simprocs + discharger
-/

/-
## Trace options

- `trace.Meta.Tactic.simp.*`
- `trace.Meta.Tactic.Debug.simp.*`

- *not* `trace.Meta.Tactic.simp.all` to enable all trace options; that's for `simp_all` only

-/
