import Mathlib.CategoryTheory.Category.Cat

namespace CategoryTheory

/-- A universe-polymorphic version of the `yoneda` specialized to `Cat`. -/
def Cat.yoneda.{v', u', v, u} : Cat.{v, u} ⥤ Cat.{v', u'}ᵒᵖ ⥤ Type (max u v u' v') where
  obj X :=
    { obj := fun Y => Y.unop ⥤ X
      map := fun f g => f.unop ⋙ g
    }
  map f :=
    { app := fun _ g => g ⋙ f }

/-- Lift the category `C : Type u` to `Type (max u u')`, and lift its arrows from `Type v` to
`Type (max v v')`. Note: this does not enforce that `C` has a `Category` instance. -/
def ULiftCat.{v', u', u} (C : Type u) : Type (max u u') :=
  let _ := ULift.{v'} Unit -- is there a better way?
  ULift.{u'} C

@[simps]
instance uliftCat.{v', u', v, u} (C : Type u) [Category.{v} C] :
    Category.{max v v'} (ULiftCat.{v', u'} C) where
  Hom X Y := ULift <| X.down ⟶ Y.down
  id X := .up <| 𝟙 X.down
  comp f g := .up <| f.down ≫ g.down

/-- Lift an object of category `C` to `ULiftCat C`. -/
def ULiftCat.up.{v', u', u} {C : Type u} (a : C) : ULiftCat.{v', u'} C := ULift.up.{u'} a

/-- Unwrap an object of category `ULiftCat C` as an object of `C`. -/
def ULiftCat.down.{v', u', u} {C : Type u} (a : ULiftCat.{v', u'} C) : C := ULift.down.{u'} a

end CategoryTheory

open CategoryTheory

universe v'₁ u'₁ v'₂ u'₂ v₁ u₁ v₂ u₂

variable {X : Type u₁} {Y : Type u₂} [Category.{v₁} X] [Category.{v₂} Y]

/-- Lifts an arrow in `C` to an arrow in `ULiftCat C`. -/
def Quiver.Hom.up {a b : X} (f : a ⟶ b) : ULiftCat.up.{v'₁, u'₁} a ⟶ .up b := ULift.up.{v'₁} f

/-- Unwraps an arrow in `ULiftCat C` as an arrow in `C`. -/
def Quiver.Hom.down {a b : X} (f : ULiftCat.up.{v'₁, u'₁} a ⟶ .up b) : a ⟶ b := ULift.down.{v'₁} f

@[simp]
theorem Quiver.Hom.id_up {a : X} : (𝟙 a).up = 𝟙 (ULiftCat.up a) := rfl

@[simp]
theorem Quiver.Hom.id_down {a : ULiftCat X} : (𝟙 a).down = 𝟙 (ULiftCat.down a) := rfl

-- !! Should these go the other way? If we drag it to the outside, it helps simp what's inside.
-- But sometimes the opposite is helpful.
@[simp]
theorem Quiver.Hom.up_congr {a b c : X} (f : a ⟶ b) (g : b ⟶ c) : f.up ≫ g.up = (f ≫ g).up := rfl

-- @[simp]
-- theorem Quiver.Hom.up_congr_symm {a b c : X} (f : a ⟶ b) (g : b ⟶ c) : (f ≫ g).up = f.up ≫ g.up  := rfl

@[simp]
theorem Quiver.Hom.down_congr {a b c : ULiftCat X} (f : a ⟶ b) (g : b ⟶ c) :
    f.down ≫ g.down = (f ≫ g).down := rfl

namespace CategoryTheory

section Functors

/-- The functor lifting objects and arrows of a category `X` to `ULiftCat X`. -/
def ULiftCat.upFunctor : X ⥤ ULiftCat.{v'₁, u'₁} X where
  obj := ULiftCat.up
  map f := f.up

/-- The functor unwrapping objects and arrows of a category `ULiftCat X` to objects and arrows in
`X`. -/
def ULiftCat.downFunctor : ULiftCat.{v'₁, u'₁} X ⥤ X where
  obj := ULiftCat.down
  map := .down

/-- The type equivalence between the objects of `X` and the objects of `ULiftCat X`. -/
def ULiftCat.equiv : X ≃ ULiftCat.{v'₁, u'₁} X where
  toFun := ULiftCat.up
  invFun := ULiftCat.down

-- Need to try all this with ULiftHom ∘ ULift instead

-- Is this kind of silly? Would be nicer to have tooling to construct these on the fly.
def Functor.up (F : X ⥤ Y) : ULiftCat.{v'₁, u'₁} X ⥤ ULiftCat.{v'₂, u'₂} Y :=
  ULiftCat.downFunctor ⋙ F ⋙ ULiftCat.upFunctor

def Functor.down (F : ULiftCat.{v'₁, u'₁} X ⥤ ULiftCat.{v'₂, u'₂} Y) : X ⥤ Y :=
  ULiftCat.upFunctor ⋙ F ⋙ ULiftCat.downFunctor

def Functor.upRight (F : X ⥤ Y) : X ⥤ ULiftCat.{v'₂, u'₂} Y :=
  F ⋙ ULiftCat.upFunctor

def Functor.upRightFunctor : (X ⥤ Y) ⥤ X ⥤ ULiftCat.{v'₂, u'₂} Y :=
  whiskeringRight _ _ _ |>.obj ULiftCat.upFunctor

def Functor.downRight (F : X ⥤ ULiftCat.{v'₂, u'₂} Y) : X ⥤ Y :=
  F ⋙ ULiftCat.downFunctor

def Functor.downRightFunctor : (X ⥤ ULiftCat.{v'₂, u'₂} Y) ⥤ X ⥤ Y :=
  whiskeringRight _ _ _ |>.obj ULiftCat.downFunctor

-- *Far* too easy to use `ULiftCat.down` when you mean `Quiver.Hom.down`. The fact that everything is ULift.down makes me think: maybe ULiftHom <| ULift is a better design.
-- Make another file testing this without ULiftCat...

-- @[simp]
-- theorem Functor.upRight_downRight_eq (F : X ⥤ Y) : F.upRight.downRight = F := rfl

/-- The bijection between functors `X ⥤ Y` and functors `X ⥤ ULiftCat Y`. -/
def Functor.upRightEquiv : X ⥤ Y ≃ X ⥤ ULiftCat.{v'₂, u'₂} Y where
  toFun := Functor.upRight
  invFun := Functor.downRight

/-- The strict equivalence between `ULiftCat (X ⥤ Y)` and `X ⥤ ULiftCat Y` internal to `Cat`. -/
def Functor.upRightIso :
    (Cat.of <| ULiftCat.{v'₂, max u'₂ v'₂} (X ⥤ Y)) ≅ (.of <| X ⥤ ULiftCat.{v'₂, u'₂} Y) where
  hom := ULiftCat.downFunctor ⋙ Functor.upRightFunctor
  inv := Functor.downRightFunctor ⋙ ULiftCat.upFunctor

def Functor.upLeft (F : X ⥤ Y) : ULiftCat.{v'₁, u'₁} X ⥤ Y :=
  ULiftCat.downFunctor ⋙ F

def Functor.downLeft (F : ULiftCat.{v'₁, u'₁} X ⥤ Y) : X ⥤ Y :=
  ULiftCat.upFunctor ⋙ F

def Functor.downLeftFunctor : (ULiftCat.{v'₁, u'₁} X ⥤ Y) ⥤ X ⥤ Y :=
  whiskeringLeft _ _ _ |>.obj ULiftCat.upFunctor

end Functors

@[simps] -- should this be named `Cat.ULift` instead?
def Cat.up.{v', u', v, u} : Cat.{v,u} ⥤ Cat.{max v v', max u u'} where
  obj C := .of <| ULiftCat.{v', u'} C
  map := Functor.up

end CategoryTheory
