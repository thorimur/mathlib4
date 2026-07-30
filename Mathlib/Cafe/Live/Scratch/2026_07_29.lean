import Lean.Elab.Command
import Lean.Elab.Tactic.BuiltinTactic
import Lean

#check Lean.TSyntax

#check Lean.MessageData.ofLazyM
#check Lean.MessageData.hasSyntheticSorry

#check Lean.Elab.Term.elabChoice
#check Lean.Elab.Term.withoutErrToSorry
#check Lean.Elab.Term.elabExplicit
#check Lean.Elab.Term.elabTerm
#check Lean.Elab.Tactic.withoutRecover
#check Lean.Elab.Tactic.runTermElab
#check Lean.Elab.Tactic.evalChoice
open Lean
-- elab "foo" : term => do
--   throwError "aaaa!"
macro "refine_liftNew " e:term : tactic => `(tactic| focus (refine @$e; rotate_right))

elab "foo_inner" : term => do
  pure (Expr.const ``id [1])

syntax "haveNew" letConfig letDecl : tactic
macro_rules
  -- special case: when given a nested `by` block, move it outside of the `refine` to enable
  -- incrementality
  | `(tactic| haveNew $c:letConfig $d:letDecl) =>
    `(tactic| refine_liftNew have $c:letConfig $d:letDecl; ?_)


#check Elab.Term.elabNoImplicitLambda
#check (fun a {b} c => true : Nat → {x : Bool} → Nat → Bool)

set_option pp.mdata true
example : {x : Nat} → True := by
  have x : Nat := _
  -- there is mdata!
  exact trivial

elab "foo" : term <= ty => do
  Elab.Term.elabTerm (← `(term|foo_inner)) ty (implicitLambda := false)

/-
When propagating result of inner elaboration, use `implicitLambda := false` and rely on the elaboration of the outer syntax to have already handled `implicitLambda` if necessary.
-/

/-
no choice node:
- elabTermAux acts on `@stx`
  → `@` tells `elabTermAux` not to run `elabImplicitLambda` on `@foo` via `blockImplicitLambda` returning true
  → `elabTermAux` runs `elabExplicit`, which is defined to call `elabTerm` on `foo` with `(implicitLambda := false)`
choice node
- elabTermAux acts on `@[choice: ..]`
  → `@` tells `elabTermAux` not to run `elabImplicitLambda` on `@foo` via `blockImplicitLambda` returning true
  → `elabTermAux` runs `elabExplicit`, which is defined to call `elabTerm` on the choice node with `(implicitLambda := false)`
  → `elabChoice` runs term elaborators for each option, but has no idea it's being called from within `elabTerm (implicitLambda := false)`, and so uses `implicitLambda := true` when it calls `elabTerm`


-/

#info_trees in
example : type_of% @id := foo_inner

#check `(example : type_of% @id := @foo)

-- elab "foo" : term => do
--   pure (Expr.const ``Bool.true [])


#check Lean.Elab.Term.elabChoice
#check realizeGlobalConst




open Lean Elab Term Tactic
def elabShow (newType : Term) : TacticM Unit := do
  evalTactic <|← `(Lean.Parser.Tactic.show| show $newType)
elab (name := «newShow») (priority := high) "show " newType:term : tactic => do
  -- let _ : MonadExceptOf Exception TacticM := MonadAlwaysExcept.except
  -- tryCatchRuntimeEx
  --   (elabShow newType)
  --   (fun ex => do logError m!"{← ex.toMessageData.format none}")

  elabShow newType

/-
1. both parsers succeed at same priority; choice node created, evalChoice invoked
2. `newShow` is run
  - `elabTerm` fails, and
    - produces a synthetic sorry in place of "hmm"
    - logs an unknown identifier error on "hmm" as message
    - hands the term off to original `show`
  - original `show` runs
    - throws an `Exception` because that synthetic sorry doesn't work in show which has messagedata which contains the synthetic sorry produced for `hmm`
      ```
      'show' tactic failed, pattern
        sorry
      is not definitionally equal to target
        True
      ```
3. That thrown exception is caught by `evalChoice`
  - `evalChoice` therefore (wrongly!) rewinds the state, which obliterates the helpful logged `hmm` error (by elabTerm)
  - then it re-throws the `show` exception.
4. Lean itself (probably during term or command elaboration?) eventually tries to turn the thrown exception into a logged error via `logAt`, but this has a guard: any MessageData that's an error with a synthetic sorry is completely ignored. Therefore, we see neither the `hmm` identifier error nor the `show` error

-/

elab "bar " t:term : tactic => do
  pure ()

elab "bar " t:term : tactic => do
  let e ← Term.elabTerm t none
  logError m!"oh no! something bad has happened!" -- sorry-free logged error message
  throwError m!"`bar` failed {e}" -- synthetic sorry in thrown exception

example : True := by
  bar (hmm + hmmmm)

#print Tactic.tryCatchRestore

#synth MonadExcept Exception TacticM

-- #check `()

#print Syntax.node2

#info_trees in
example : True := by
  show hmm

#check `(command|example : False := by
  show arbitrary_ident)
