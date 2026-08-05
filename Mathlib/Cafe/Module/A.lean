module

import Mathlib.Cafe.Repr

@[reducible] public def foo (n : Nat) : Nat := n + 1

public theorem foo_eq : foo 5 = 6 := (rfl)

-- #check Lean.Environment

public section

inductive Bar where
| mk (n : Nat) : Bar

instance instInhabitedBar : Inhabited Bar := ⟨.mk 0⟩

open Lean

-- run_cmd do
--   let some c := (← getEnv).find? ``instInhabitedBar | throwError "Couldn't find it!"
--   let e := (← getEnv).hasExposedBody ``instInhabitedBar
--   logInfo m!"exposed: {e}: {repr c}"

/-
1. name
    ↓ .type
2. type

3. @[expose]: value
3a. name [unfold]↦ value
    - transparency settings control when!
      - reducible

-/

public def foo₁ {a : Nat} : Bool := false

@[implicit_reducible] def a : Nat := 5

private def myParticularNameForAPrivateDef := true

example : @foo₁ a = @foo₁ 5 := by with_reducible rfl

-- TODO: what????
theorem one_eq_one_and : 1 = 1 ∧ 2 = 2 := And.intro rfl rfl

def matchOneEqOneAnd (h : 1 = 1 ∧ 2 = 2) : Bool := h.rec fun _ _ => true

#guard_msgs (drop error) in
example : matchOneEqOneAnd one_eq_one_and = true := by
  with_unfolding_all rfl'

-- Qs: turning Acc into type intead of prop related?

/-
# TransparencyMode: ambient, in context during defeq
# ReducibilityStatus: attached to declaration
mode:                       none < reducible    < instances
decls that can be unfolded: ∅    < @[reducible] < + @[instance_reducible]

< implicit                < default             < all
< + @[implicit_reducible] < + @[semireducible]  < + @[irreducible] *and* theorems!

-/

-- run_cmd do
--   let some c := (← getEnv).find? ``a | throwError "Couldn't find it!"
--   let reducibility := getReducibilityStatusCore (← getEnv) ``a
--   logInfo m!"reducibility: {repr reducibility} {repr c}"

/-
foo' {a : Nat} : a = , foo {a : Nat}

foo
-/

-- #print Meta.TransparencyMode

-- run_cmd do
--   let some c := (← getEnv).find? ``foo | throwError "Couldn't find it!"
--   logInfo m!"{repr c}"
