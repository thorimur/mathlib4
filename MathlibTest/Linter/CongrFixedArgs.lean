import Mathlib.Tactic.Linter.CongrFixedArgs
import Mathlib.Init

set_option linter.congrFixedArgs true

def myMap (f : Nat → Nat) (l' : List Nat) : List Nat := l'.map f

/--
warning: The `@[congr]` theorem `myMap_congr` does not allow the following explicit arguments of `myMap` to change:
  `l : List Nat`
This violates the recommendation in the documentation of `@[congr]`.

Note: This linter can be disabled with `set_option linter.congrFixedArgs false`
-/
#guard_msgs in
@[congr]
theorem myMap_congr {f g : Nat → Nat} {l : List Nat} (h : ∀ x ∈ l, f x = g x) :
    myMap f l = myMap g l :=
  List.map_congr_left h

-- Every explicit argument changes: no warning.
#guard_msgs in
@[congr]
theorem myMap_congr' {f g : Nat → Nat} {l l' : List Nat} (hl : l = l')
    (h : ∀ x ∈ l', f x = g x) : myMap f l = myMap g l' := by
  subst hl
  exact List.map_congr_left h

theorem myMap_congr'' {f g : Nat → Nat} {l : List Nat} (h : ∀ x ∈ l, f x = g x) :
    myMap f l = myMap g l :=
  List.map_congr_left h

#check Lean.registerBuiltinAttribute
#check Lean.Syntax.eqWithInfo


inductive Description where
  | thing (α : Type) (inst : DecidableEq α) (x : Description)
  | base

#check Quotient.lift

inductive Mix : Description × Type → Type 1 where
  | nat (f :  → Nat) : Mix (.base, Nat)
  | list (α : Type) {inst : DecidableEq α} (x : α) (r : Mix (desc, β)) :
    Mix (.thing α inst desc, List β)

inductive Vec (α) : Nat → Type where
  | cons : α → Vec α n → Vec α (n+1)
  | nil : Vec α 0

#check Lean.Meta.unifyEq?
#check Eq.rec
example {α α' : Type} : True := by
  cases h
example (a b : Vec α d) : True := by
  cases a
  · cases b

  · cases b

def decHEqMix (a : Mix d) (b : Mix d') (h : d.1 = d'.1) : Decidable (a ≍ b ∧ d.2 = d'.2) := by
  cases a with
  | nat =>
    cases b
    · exact isTrue ⟨.rfl, rfl⟩
    · injection h
  | @list _ β α _ x r =>
    cases b with
    | nat => injection h
    | @list _ β' α' _ x' r' =>
      injection h with hα hinst hdesc
      subst hα hinst hdesc
      by_cases hx : x = x'
      · have := decHEqMix r r' rfl
        by_cases hrβ : r ≍ r' ∧ β = β'
        · subst hx
          have hr := hrβ.left
          have hβ := hrβ.right
          subst hβ
          subst hr
          exact isTrue ⟨.rfl, rfl⟩
        · refine isFalse ?_
          grind
      · refine isFalse ?_
        grind



set_option trace.debug true



#check Lean.Elab.Term.BinderView
#check Lean.mkIdentFromRef

open Lean Elab Syntax
#check mkIdentFrom <|← Lean.MonadQuotation.addMacroScope `inst
@[congr]
theorem myMap_congr'''' [Nonempty Nat] {f g : Nat → Nat} {l : List Nat} (h : ∀ x ∈ l, f x = g x) :
    myMap f l = myMap g l :=
  List.map_congr_left h

theorem MyNamespace.myMap_congr''' {f g : Nat → Nat} {l : List Nat} (h : ∀ x ∈ l, f x = g x) :
    myMap f l = myMap g l :=
  List.map_congr_left h

-- /--
-- warning: The `@[congr]` theorem `myMap_congr''` does not allow the following explicit arguments of `myMap` to change:
--   `l : List Nat`
-- This violates the recommendation in the documentation of `@[congr]`.

-- Note: This linter can be disabled with `set_option linter.congrFixedArgs false`
-- -/
-- #guard_msgs in
-- attribute [congr] myMap_congr''

attribute [local congr] myMap_congr'' myMap_congr'''' in
example : True := trivial

def myZipWith (f : Nat → Nat → Nat) (l₁ l₂ : List Nat) : List Nat := List.zipWith f l₁ l₂

/--
warning: The `@[congr]` theorem `myZipWith_congr` does not allow the following explicit arguments of `myZipWith` to change:
  `l₁ : List Nat`
  `l₂ : List Nat`
This violates the recommendation in the documentation of `@[congr]`.

Note: This linter can be disabled with `set_option linter.congrFixedArgs false`
-/
#guard_msgs in
@[congr]
theorem myZipWith_congr {f g : Nat → Nat → Nat} {l₁ l₂ : List Nat} (h : ∀ a b, f a b = g a b) :
    myZipWith f l₁ l₂ = myZipWith g l₁ l₂ := by
  have : f = g := funext fun a ↦ funext (h a)
  rw [this]

def myGet (l : List Nat) (i : Nat) (_h : i < l.length) : Nat := l[i]

-- Proof arguments are ignored, even when they are the same on both sides.
#guard_msgs in
@[congr]
theorem myGet_congr {l l' : List Nat} {i i' : Nat} (hl : l = l') (hi : i = i')
    (h : i < l.length) : myGet l i h = myGet l' i' (hl ▸ hi ▸ h) := by
  subst hl hi
  rfl
