/-
Copyright (c) 2021 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn, Kim Morrison
-/
module

public import Mathlib.Data.Opposite
public import Mathlib.Tactic.ToDual

/-!
# Quivers

This module defines quivers. A quiver on a type `V` of vertices assigns to every
pair `a b : V` of vertices a type `a ⟶ b` of arrows from `a` to `b`. This
is a generalization of `Digraph V`, which can be thought of as "a proposition `a ⟶ b` of arrows".

-/

@[expose] public section

open Opposite

-- We use the same universe order as in category theory.
-- See note [category theory universes]
universe v v₁ v₂ u u₁ u₂

/-- A quiver `G` on a type `V` of vertices assigns to every pair `a b : V` of vertices
a type `a ⟶ b` of arrows from `a` to `b`. This is hence a form of directed multigraphs.

For graphs with no repeated edges, one can either use `Quiver.IsThin` to demand
that the hom sets are subsingletons, or `Digraph V` (where the hom sets
are Prop-valued).

Because `Category` will later extend this class, we call the field `Hom`.
Except when constructing instances, you should rarely see this, and use the `⟶` notation instead.
-/
class Quiver (V : Type u) where
  /-- The type of edges/arrows/morphisms between a given source and target. -/
  HomType : V → V → Type v

@[ext]
structure Quiver.Hom {V} [Quiver V] (a b : V) where
  val : Quiver.HomType a b

attribute [to_dual self (reorder := 3 4)] Quiver.HomType
attribute [to_dual self (reorder := HomType (1 2))] Quiver.mk

attribute [to_dual self (reorder := a b)] Quiver.Hom
attribute [to_dual self] Quiver.Hom.mk
attribute [to_dual self] Quiver.Hom.val

def Quiver.Hom.map {V} {a b : V} [Quiver V] (f : Quiver.HomType a b → Quiver.HomType a b)
    (arr : Quiver.Hom a b) : Quiver.Hom a b where
  val := f arr.val

def Quiver.Hom.hmap {V} {a₀ b₀ a₁ b₁ : V} [Quiver V]
    (f : Quiver.HomType a₀ b₀ → Quiver.HomType a₁ b₁)
    (arr : Quiver.Hom a₀ b₀) : Quiver.Hom a₁ b₁ where
  val := f arr.val

/--
Notation for the type of edges/arrows/morphisms between a given source and target
in a quiver or category.
-/
infixr:10 " ⟶ " => Quiver.Hom

namespace Quiver

/-- `Vᵒᵖ` reverses the direction of all arrows of `V`. -/
instance opposite {V} [Quiver V] : Quiver Vᵒᵖ :=
  ⟨fun a b => HomType (unop b) (unop a)⟩

/-- The opposite of an arrow in `V`. -/
@[to_dual self]
nonrec def Hom.op {V} [Quiver V] {X Y : V} (f : X ⟶ Y) : op Y ⟶ op X := ⟨f.val⟩

/-- Given an arrow in `Vᵒᵖ`, we can take the "unopposite" back in `V`. -/
@[to_dual self]
def Hom.unop {V} [Quiver V] {X Y : Vᵒᵖ} (f : X ⟶ Y) : unop Y ⟶ unop X := ⟨f.val⟩

/-- The bijection `(X ⟶ Y) ≃ (op Y ⟶ op X)`. -/
@[simps, to_dual self]
def Hom.opEquiv {V} [Quiver V] {X Y : V} : (X ⟶ Y) ≃ (Opposite.op Y ⟶ Opposite.op X) where
  toFun := Quiver.Hom.op
  invFun := Quiver.Hom.unop

/-- A type synonym for a quiver with no arrows. -/
def Empty (V : Type u) : Type u := V

instance emptyQuiver (V : Type u) : Quiver.{u} (Empty V) := ⟨fun _ _ => PEmpty⟩

@[simps, to_dual self]
def emptyArrowEquiv {V : Type u} (a b : Empty V) : (a ⟶ b) ≃ PEmpty where
  toFun := nofun
  invFun := nofun
  left_inv := nofun
  right_inv := nofun

/-- A quiver is thin if it has no parallel arrows. -/
abbrev IsThin (V : Type u) [Quiver V] : Prop := ∀ a b : V, Subsingleton (a ⟶ b)

to_dual_insert_cast_fun IsThin := fun inst a b ↦ inst b a, fun inst a b ↦ inst b a


section

variable {V : Type*} [Quiver V] {X Y X' Y' : V}

/-- An arrow in a quiver can be transported across equalities between the source and target
objects. -/
@[to_dual self (reorder := X Y, X' Y', hX hY)]
def homOfEq (f : X ⟶ Y) (hX : X = X') (hY : Y = Y') : X' ⟶ Y' := by
  subst hX hY
  exact f

@[simp, to_dual self]
lemma homOfEq_trans (f : X ⟶ Y) (hX : X = X') (hY : Y = Y')
    {X'' Y'' : V} (hX' : X' = X'') (hY' : Y' = Y'') :
    homOfEq (homOfEq f hX hY) hX' hY' = homOfEq f (hX.trans hX') (hY.trans hY') := by
  subst hX hY hX' hY'
  rfl

@[to_dual self]
lemma homOfEq_injective (hX : X = X') (hY : Y = Y')
    {f g : X ⟶ Y} (h : Quiver.homOfEq f hX hY = Quiver.homOfEq g hX hY) : f = g := by
  subst hX hY
  exact h

@[simp, to_dual self]
lemma homOfEq_rfl (f : X ⟶ Y) : Quiver.homOfEq f rfl rfl = f := rfl

@[to_dual self]
lemma heq_of_homOfEq_ext (hX : X = X') (hY : Y = Y') {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (e : Quiver.homOfEq f hX hY = f') : f ≍ f' := by
  subst hX hY
  rw [Quiver.homOfEq_rfl] at e
  rw [e]

@[to_dual self]
lemma homOfEq_eq_iff (f : X ⟶ Y) (g : X' ⟶ Y') (hX : X = X') (hY : Y = Y') :
    Quiver.homOfEq f hX hY = g ↔ f = Quiver.homOfEq g hX.symm hY.symm := by
  subst hX hY; simp

@[to_dual self]
lemma eq_homOfEq_iff (f : X ⟶ Y) (g : X' ⟶ Y') (hX : X' = X) (hY : Y' = Y) :
    f = Quiver.homOfEq g hX hY ↔ Quiver.homOfEq f hX.symm hY.symm = g := by
  subst hX hY; simp

@[to_dual self]
lemma homOfEq_heq (hX : X = X') (hY : Y = Y') (f : X ⟶ Y) : homOfEq f hX hY ≍ f :=
  (heq_of_homOfEq_ext hX hY rfl).symm

@[to_dual self]
lemma homOfEq_heq_left_iff (f : X ⟶ Y) (g : X' ⟶ Y') (hX : X = X') (hY : Y = Y') :
    homOfEq f hX hY ≍ g ↔ f ≍ g := by
  cases hX; cases hY; rfl

@[to_dual self]
lemma homOfEq_heq_right_iff (f : X ⟶ Y) (g : X' ⟶ Y') (hX : X' = X) (hY : Y' = Y) :
    f ≍ homOfEq g hX hY ↔ f ≍ g := by
  cases hX; cases hY; rfl


end

end Quiver
