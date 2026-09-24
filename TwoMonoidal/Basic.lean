import Mathlib.CategoryTheory.Monoidal.Category

set_option linter.style.header false
set_option linter.style.longLine false

universe v u

namespace CategoryTheory

open scoped MonoidalCategory

-- Define two monoidal structures on one category
structure TwoMonoidalStructures
    (C : Type u) [Category.{v} C] where
  tensor₁ : MonoidalCategory C
  tensor₂ : MonoidalCategory C


namespace TwoMonoidalStructures

variable {C : Type u} [Category.{v} C]

-- Tensor₁ of objects
abbrev tensorObj₁
    (M : TwoMonoidalStructures C) (X Y : C) : C :=
  letI : MonoidalCategory C := M.tensor₁
  X ⊗ Y

-- Tensor₂ of objects
abbrev tensorObj₂
    (M : TwoMonoidalStructures C) (X Y : C) : C :=
  letI : MonoidalCategory C := M.tensor₂
  X ⊗ Y

-- Notation for tensors of objects
local notation:70 X:71 " ⊗₁[" M "] " Y:71 =>
  TwoMonoidalStructures.tensorObj₁ M X Y

local notation:70 X:71 " ⊗₂[" M "] " Y:71 =>
  TwoMonoidalStructures.tensorObj₂ M X Y

-- Tensor₁ unit
abbrev tensorUnit₁ (M : TwoMonoidalStructures C) : C :=
  letI : MonoidalCategory C := M.tensor₁
  𝟙_ C

-- Tensor₂ unit
abbrev tensorUnit₂ (M : TwoMonoidalStructures C) : C :=
  letI : MonoidalCategory C := M.tensor₂
  𝟙_ C

-- Notation for tensor units
local notation:71 " 𝟙⊗₁[" M "] " =>
  TwoMonoidalStructures.tensorUnit₁ M

local notation:71 " 𝟙⊗₂[" M "] " =>
  TwoMonoidalStructures.tensorUnit₂ M

-- Tensor₁ of morphisms
abbrev tensorHom₁
    (M : TwoMonoidalStructures C)
    {X₁ Y₁ X₂ Y₂ : C}
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    X₁ ⊗₁[M] X₂ ⟶ Y₁ ⊗₁[M] Y₂ := by
  letI : MonoidalCategory C := M.tensor₁
  exact f ⊗ₘ g

-- Tensor₂ of morphisms
abbrev tensorHom₂
    (M : TwoMonoidalStructures C)
    {X₁ Y₁ X₂ Y₂ : C}
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    X₁ ⊗₂[M] X₂ ⟶ Y₁ ⊗₂[M] Y₂ := by
  letI : MonoidalCategory C := M.tensor₂
  exact f ⊗ₘ g

-- Notation for tensors of morphisms
local notation:70 f " ⊗₁ₘ[" M "] " g =>
  TwoMonoidalStructures.tensorHom₁ M f g

local notation:70 f " ⊗₂ₘ[" M "] " g =>
  TwoMonoidalStructures.tensorHom₂ M f g

-- Helper functions for associators
abbrev tensorAssociator₁
    (M : TwoMonoidalStructures C) (X Y Z : C) :
    (X ⊗₁[M] Y) ⊗₁[M] Z ≅ X ⊗₁[M] (Y ⊗₁[M] Z) := by
  letI : MonoidalCategory C := M.tensor₁
  exact α_ X Y Z

abbrev tensorAssociator₂
    (M : TwoMonoidalStructures C) (X Y Z : C) :
    (X ⊗₂[M] Y) ⊗₂[M] Z ≅ X ⊗₂[M] (Y ⊗₂[M] Z) := by
  letI : MonoidalCategory C := M.tensor₂
  exact α_ X Y Z

-- Helper functions for unitors
abbrev tensorrightUnitor₁
    (M : TwoMonoidalStructures C) (X : C) :
    X ⊗₁[M] (𝟙⊗₁[M]) ≅ X := by
  letI : MonoidalCategory C := M.tensor₁
  exact ρ_ X

abbrev tensorleftUnitor₁
    (M : TwoMonoidalStructures C) (X : C) :
    (𝟙⊗₁[M]) ⊗₁[M] X ≅ X := by
  letI : MonoidalCategory C := M.tensor₁
  exact λ_ X

abbrev tensorrightUnitor₂
    (M : TwoMonoidalStructures C) (X : C) :
    X ⊗₂[M] (𝟙⊗₂[M]) ≅ X := by
  letI : MonoidalCategory C := M.tensor₂
  exact ρ_ X

abbrev tensorleftUnitor₂
    (M : TwoMonoidalStructures C) (X : C) :
    (𝟙⊗₂[M]) ⊗₂[M] X ≅ X := by
  letI : MonoidalCategory C := M.tensor₂
  exact λ_ X

-- Helper functions for whiskering
abbrev tensorwhiskerLeft₁ (M : TwoMonoidalStructures C) (X : C) {Y₁ Y₂ : C} (f : Y₁ ⟶ Y₂) : X ⊗₁[M] Y₁ ⟶ X ⊗₁[M] Y₂ := by
  letI : MonoidalCategory C := M.tensor₁
  exact X ◁ f

abbrev tensorwhiskerRight₁ (M : TwoMonoidalStructures C) {X₁ X₂ : C} (Y : C) (f : X₁ ⟶ X₂) : X₁ ⊗₁[M] Y ⟶ X₂ ⊗₁[M] Y := by
  letI : MonoidalCategory C := M.tensor₁
  exact f ▷ Y

abbrev tensorwhiskerLeft₂ (M : TwoMonoidalStructures C) (X : C) {Y₁ Y₂ : C} (f : Y₁ ⟶ Y₂) : X ⊗₂[M] Y₁ ⟶ X ⊗₂[M] Y₂ := by
  letI : MonoidalCategory C := M.tensor₂
  exact X ◁ f

abbrev tensorwhiskerRight₂ (M : TwoMonoidalStructures C) {X₁ X₂ : C} (Y : C) (f : X₁ ⟶ X₂) : X₁ ⊗₂[M] Y ⟶ X₂ ⊗₂[M] Y := by
  letI : MonoidalCategory C := M.tensor₂
  exact f ▷ Y

abbrev tensorwhiskerLeftIso₁ (M : TwoMonoidalStructures C) (X : C) {Y₁ Y₂ : C} (f : Y₁ ≅ Y₂) : X ⊗₁[M] Y₁ ≅ X ⊗₁[M] Y₂ := by
  letI : MonoidalCategory C := M.tensor₁
  exact X ◁ᵢ f

abbrev tensorwhiskerRightIso₁ (M : TwoMonoidalStructures C) {X₁ X₂ : C} (Y : C) (f : X₁ ≅ X₂) : X₁ ⊗₁[M] Y ≅ X₂ ⊗₁[M] Y := by
  letI : MonoidalCategory C := M.tensor₁
  exact f ▷ᵢ Y

abbrev tensorwhiskerLeftIso₂ (M : TwoMonoidalStructures C) (X : C) {Y₁ Y₂ : C} (f : Y₁ ≅ Y₂) : X ⊗₂[M] Y₁ ≅ X ⊗₂[M] Y₂ := by
  letI : MonoidalCategory C := M.tensor₂
  exact X ◁ᵢ f

abbrev tensorwhiskerRightIso₂ (M : TwoMonoidalStructures C) {X₁ X₂ : C} (Y : C) (f : X₁ ≅ X₂) : X₁ ⊗₂[M] Y ≅ X₂ ⊗₂[M] Y := by
  letI : MonoidalCategory C := M.tensor₂
  exact f ▷ᵢ Y

end TwoMonoidalStructures

end CategoryTheory
