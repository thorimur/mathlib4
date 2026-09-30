import Lean
open Lean Meta Elab Tactic Sym
/- Hi! -/

open Lean Meta Elab Tactic Sym


/- Hi! -/

/-
For anyone new to metaprogramming:

Lean type theory terms are `Lean.Expr`s
-/
#print Lean.Expr
/-
A metavariable is a typed hole in an expression during meta actions, which may be assigned, and then replaced with that assignment in the `Expr` via `instantiateMVars`
-/

-- Checks if two expr's are definitionally equal, involves some unfolding + mvar unification etc.
-- Expensive!
#check Lean.Meta.isDefEq
-- Instead, `SymM` maximally shares terms which lets us use pointer comparisons instead of defeq


-- maximal sharing: https://arxiv.org/pdf/2003.01685 graphs on page 6

/--
info: @[reducible] def Lean.Meta.Sym.SymM : Type → Type :=
ReaderT Sym.Context (StateRefT' IO.RealWorld Sym.State MetaM)
-/
#guard_msgs in
#print SymM

/-- info: Lean.Meta.Sym.SymM (α : Type) : Type -/
#guard_msgs in
#check SymM
/-- info: Lean.Meta.Sym.SymM.run {α : Type} (x : SymM α) : MetaM α -/
#guard_msgs in
#check SymM.run
/-- info: Lean.Meta.Sym.share (e : Expr) : SymM Expr -/
#guard_msgs in
#check Sym.share

/-- info: true -/
#guard_msgs in
#eval SymM.run do
  let e1 ← Sym.share <| mkConst ``Nat
  let e2 ← Sym.share <| mkConst ``Nat
  return isSameExpr e1 e2

-- Allows us to share all the expressions associated with the metavariable (lctx, etc.)
/-- info: Lean.Meta.Sym.preprocessMVar (mvarId : MVarId) : SymM MVarId -/
#guard_msgs in
#check Sym.preprocessMVar

/-- info: false -/
#guard_msgs in
#eval SymM.run do
  let m₁ ← Sym.preprocessMVar <| (← mkFreshExprMVar (mkConst ``Nat)).mvarId!
  let m₂ ← Sym.share <| ← mkFreshExprMVar (mkConst ``Nat)
  return isSameExpr (.mvar m₁) (m₂)

-- Context in SymM grows only monotonically. Means that we cannot throw away fvars and that therefore the concept of a "maximum fvar" is meaningful and can be used for O(1) assignability checks (to ensure well-formedness(?))

-- Shrinking the context is in general useful. Induction (at least as we're usually familiar with it) does this, reverting anything...rewriting and removing the previous hypothesis. Maybe there are ways around this, like pretending previous fvars aren't there

-- TODO: read huge docstring in src/Lean/Meta/Sym.lean
-- Note: `GrindM` is on top of `SymM`

-- `SymM` is for high-perf automation and will not warn you if you screw up.
-- In particular, you can call `MetaM` things, and they will appear fine even if they might not be.
-- Strat: encapsulate the meta actions, then share whatever proof they produce, for instance. Just don't do it within `SymM` and mess up your `SymM` state!


/-! # `simp` -/

/- The proof of equality in `Result` does *not* need to be shared. (But may become shared when within a non-proof that gets shared, such as the `h` in `xs[i]'h`) -/

#check Sym.Simp.Result
#check Sym.simp -- entrypoint to Sym's `simp`
#check Sym.simpGoal -- another entrypoint to Sym's `simp`, thin wrapper around `Sym.simp`
/--
info: @[reducible] def Lean.Meta.Sym.Simp.Simproc : Type :=
Expr → Sym.Simp.SimpM Sym.Simp.Result
-/
#guard_msgs in
#print Sym.Simp.Simproc

/-
inductive Result where
  /-- No change. If `done = true`, skip remaining simplification steps for this term. -/
  | rfl (done : Bool := false) (contextDependent : Bool := false)
  /--
  Simplified to `e'` with proof `proof : e = e'`.
  If `done = true`, skip recursive simplification of `e'`. -/
  | step (e' : Expr) (proof : Expr) (done : Bool := false) (contextDependent : Bool := false)
-/



#check eq_self

def mySimproc : Sym.Simp.Simproc := fun e => do
  let_expr c@Eq α lhs rhs := e | return .rfl
  if !isSameExpr lhs rhs then return .rfl
  let e' ← Sym.share <| mkConst ``True
  let proof := mkApp2 (mkConst ``eq_self c.constLevels!) α lhs
  return .step e' proof true false

elab "sym_simp" : tactic => do
  liftMetaTactic1 fun mvarId => do
    SymM.run do
      -- simp only does what you specify, so you need to specify reductions yourself
      let methods : Sym.Simp.Methods := { post := Sym.Simp.beta >> Sym.Simp.evalGround >> mySimproc }
      let mvarId ← Sym.preprocessMVar mvarId
      (← Sym.simpGoal mvarId methods).toOption

-- does beta reduction and ground term evaluation because we told it to
-- but doesn't reduce lets because we didn't tell it to

/--
error: unsolved goals
a b c : Nat
⊢ if True then True
  else
    b =
      let x := 0;
      c
-/
#guard_msgs in
example (a b c : Nat) : if (fun a => a) a = a then 10 - 9 - 1 = 0 else b = let x := 0; c := by
  sym_simp

-- you can use `Theorems.rewrite` for rewriting using theorems
-- you still need to do some preprocessing yourself
-- but it will e.g. do ground reduction during pattern matching itself

elab "sym_simp_theorems" : tactic => do
  liftMetaTactic1 fun mvarId => do
    SymM.run do
      let mut thms : Sym.Simp.Theorems := {}
      thms := thms.insert (← Sym.Simp.mkTheoremFromDecl ``eq_self)
      let methods : Sym.Simp.Methods := { post := thms.rewrite }
      let mvarId ← Sym.preprocessMVar mvarId
      (← Sym.simpGoal mvarId methods).toOption

/--
error: unsolved goals
a b c : Nat
⊢ if (fun a => a) a = a then True else b = c
-/
#guard_msgs in
example (a b c : Nat) : if (fun a => a) a = a then 10 - 9 - 1 = 0 else b = have x := 0; c := by
  sym_simp_theorems

/-

 def symIntToBitVecName : Name := `int_toBitVec_sym
 def metaIntToBitVecName : Name := `int_toBitVec_meta

 builtin_initialize symIntToBitVecExt : Sym.Simp.SymSimpExtension ←
   Sym.Simp.registerSymSimpAttr symIntToBitVecName "sym simp theorems used to convert UIntX/IntX statements into BitVec ones"

 builtin_initialize metaIntToBitVecExt : Meta.SimpExtension ←
   Meta.registerSimpAttr metaIntToBitVecName "meta simp theorems used to convert UIntX/IntX statements into BitVec ones"
-/

-- ordinary simproc uses discrtree patterns:
-- simproc foo (And _ _) := sorry
-- Sym.Simp.Simproc doesn't! Or, if you want it, you must create it yourself
-- This is part of
#check Sym.Simp.Theorems

/-
In `Theorem`, matching through `Pattern` (which contains nice precomputed data to replace defeq matches) is weaker, but faster
-/
-- To get a simproc:
#check Sym.Simp.Theorems.rewrite

/-
Most simprocs exit early. Not having a discrtree and exiting early (then linearly just going to the next simproc via `andThen`) is usually faster.
-/

#print Pattern
-- Entry point:
#print Pattern.match?
-- ^ Tells you if it sym-unifies

-- `sym =>` uses `: grind` syntax category
-- sym extensions exist to allow you to maintain custom state within `sym =>`
-- `@[grind_tactic ]`

syntax (name := symTest) "sym_test" : grind

open Grind
#check GrindTactic
#check GrindTacticM
#check GrindM -- can lift to `GrindTacticM`

@[grind_tactic symTest] def symTestElab : GrindTactic := fun _ => return

example : False := by
  sym =>
    sym_test

-- Grind triggers:
/-

instantiate bound variables in a quantifier
unconditional translation between theories is generally a bad idea, e.g. moving from statements about drop to statements about extract (assuming they are different)
What a good trigger is is basically impossible to figure out in principle. experimentation instead!

`grind_pattern` lets you define arbitrary triggers via e.g. guards against (sym) defeq etc.
-/
