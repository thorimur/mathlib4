module

import Lean

/-
- `logInfo`/logs
- `dbg_trace`
- `trace[debug]`/`trace[<trace_cls>]`
-/

open Lean

-- set_option trace.Meta.isDefEq true

/--
info: Lean.withTraceNode {α : Type} {m : Type → Type} [Monad m] [MonadTrace m] [MonadRef m] [AddMessageContext m]
  [MonadOptions m] {ε : Type} [always : MonadAlwaysExcept ε m] [MonadLiftT BaseIO m] [ExceptToTraceResult ε α]
  (cls : Name) (msg : Except ε α → m MessageData) (k : m α) (collapsed : Bool := true) (tag : String := "") : m α
-/
#guard_msgs in
#check withTraceNode

run_cmd
  let stx ← `(term| foo + 1)
  logInfo m!"{repr stx}"

set_option trace.debug true
-- set_option trace.profiler true

run_cmd
  let e := Expr.const ``Bool.true []
  withTraceNode `debug (fun _ => return m!"Something happened!") (tag := "foo") do
    trace[debug] "expression: {e}"

initialize registerTraceClass `mytraceclass

-- set_option trace.mytraceclass true
-- set_option trace.profiler true

set_option verbose false

#check ∀ (x x : Nat), Fin (x + clear% x; x)

#check Lean.DataValue

/-- A docstring! -/
register_option myOption : Syntax := {
  defValue := .missing
  descr := "A...second docstring?"
}



public section

#check Name

inductive A where
| mk (n : Nat) {hash} (hash_eq_toUInt64 : hash = n.toUInt64 := by rfl)
| mk' (b : Bool) {hash} (hash_eq_toUInt64 : hash = if b then 0 else 1 := by rfl)
-- with @[computed_field] protected hash : A → UInt64
--   | .mk n => n.toUInt64
--   | .mk' b => if b then 0 else 1

example : A → Bool
  | .mk n => true
  | .mk' b => b
namespace Foo

mutual

def hash : Name → UInt64
  | .anonymous => .ofNatLT 1723 (of_decide_eq_true rfl)
  | .str p s => mixHash p.hash s.hash
  | .num p v => mixHash p.hash (dite (LT.lt v UInt64.size) (fun h => UInt64.ofNatLT v h) (fun _ => UInt64.ofNatLT 17 (of_decide_eq_true rfl)))

inductive Name where
  | anonymous {h} (hash_eq : h = hash .anonymous := by rfl) : Name
  | str (pre : Name) (str : String) {h} (hash_eq : h = hash (.str pre str) := by rfl)
  | num (pre : Name) (i : Nat) {h} (hash_eq : h = hash (.num pre i) := by rfl)

end

#print A.mk._impl

#print Name
#print Name._impl

#print Expr
#print Expr._impl

/--
error:
# Alert

**Don't use this!**
-/
#guard_msgs in
run_cmd
  logError m!"\n\
  # Alert\n\n\
  **Don't use this!**"

set_option trace.Compiler.result true

#print A.mk._override

def myA : A := .mk 5



open Elab Command
run_cmd
  modifyScope fun s =>
    { s with opts := s.opts.insert `pp.piPreserveNames true }

#check ∀ (x x : Nat), Fin (x + clear% x; x)

run_cmd
  let e := Expr.const ``Bool.true []
  withTraceNode `mytraceclass (fun _ => return m!"Something happened!") (tag := "foo") do
    IO.sleep 1
    trace[mytraceclass] "expression: {e}"
