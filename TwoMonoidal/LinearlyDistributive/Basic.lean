import Mathlib.CategoryTheory.Monoidal.Category
import TwoMonoidal.Basic

set_option linter.style.header false
set_option linter.style.longLine false

namespace CategoryTheory
namespace LinDistCategory

scoped notation:70 X:71 " ⊗[" M "] " Y:71 =>
  TwoMonoidalStructures.tensorObj₁ M X Y

scoped notation:70 X:71 " ⅋[" M "] " Y:71 =>
  TwoMonoidalStructures.tensorObj₂ M X Y

scoped notation:max " 𝟙⊗[" M "] " =>
  TwoMonoidalStructures.tensorUnit₁ M

scoped notation:max " 𝟙⅋[" M "] " =>
  TwoMonoidalStructures.tensorUnit₂ M

scoped notation:70 f:71 " ⊗ₘ[" M "] " g:70 =>
  TwoMonoidalStructures.tensorHom₁ M f g

scoped notation:70 f:71 " ⅋ₘ[" M "] " g:70 =>
  TwoMonoidalStructures.tensorHom₂ M f g

scoped notation "α⊗[" M "]" =>
  TwoMonoidalStructures.tensorAssociator₁ M

scoped notation "α⅋[" M "]" =>
  TwoMonoidalStructures.tensorAssociator₂ M

scoped notation:81 X:71 "◁⊗[" M "]" f:70 =>
  TwoMonoidalStructures.tensorwhiskerLeft₁ M X f

scoped notation:81 f:71 "▷⊗[" M "]" Y:70 =>
  TwoMonoidalStructures.tensorwhiskerRight₁ M Y f

scoped notation:81 X:71 "◁⅋[" M "]" f:70 =>
  TwoMonoidalStructures.tensorwhiskerLeft₂ M X f

scoped notation:81 f:71 "▷⅋[" M "]" Y:70 =>
  TwoMonoidalStructures.tensorwhiskerRight₂ M Y f

scoped notation:81 X:71 "◁⊗ᵢ[" M "]" f:70 =>
  TwoMonoidalStructures.tensorwhiskerLeftIso₁ M X f

scoped notation:81 f:71 "▷⊗ᵢ[" M "]" Y:70 =>
  TwoMonoidalStructures.tensorwhiskerRightIso₁ M Y f

scoped notation:81 X:71 "◁⅋ᵢ[" M "]" f:70 =>
  TwoMonoidalStructures.tensorwhiskerLeftIso₂ M X f

scoped notation:81 f:71 "▷⅋ᵢ[" M "]" Y:70 =>
  TwoMonoidalStructures.tensorwhiskerRightIso₂ M Y f

scoped notation "ρ⊗[" M "]" =>
  TwoMonoidalStructures.tensorrightUnitor₁ M

scoped notation "λ⊗[" M "]" =>
  TwoMonoidalStructures.tensorleftUnitor₁ M

scoped notation "ρ⅋[" M "]" =>
  TwoMonoidalStructures.tensorrightUnitor₂ M

scoped notation "λ⅋[" M "]" =>
  TwoMonoidalStructures.tensorleftUnitor₂ M

end LinDistCategory

open LinDistCategory

-- Underlying structure of Lin Dist cats
class LinDistCategoryStruct (C : Type u) [Category.{v} C] (M : TwoMonoidalStructures C) where
  leftDistributor : ∀ X Y Z : C, X ⊗[M] (Y ⅋[M] Z) ⟶ (X ⊗[M] Y) ⅋[M] Z
  rightDistributor: ∀ X Y Z : C, (X ⅋[M] Y) ⊗[M] Z ⟶ X ⅋[M] (Y ⊗[M] Z)

namespace LinDistCategory

-- scoped notation " δₗ[" M "]" =>
--   LinDistCategoryStruct.leftDistributor (M := M)

-- scoped notation " δᵣ[" M "]" =>
--   LinDistCategoryStruct.rightDistributor (M := M)

variable {C : Type u} [Category.{v} C]
variable {M : TwoMonoidalStructures C}

def left_Distributor
    (M : TwoMonoidalStructures C)
    [D : LinDistCategoryStruct C M] :=
  D.leftDistributor

def right_Distributor
    (M : TwoMonoidalStructures C)
    [D : LinDistCategoryStruct C M] :=
  D.rightDistributor

scoped notation:max " δₗ[" M "]" => left_Distributor M
scoped notation:max " δᵣ[" M "]" => right_Distributor M

end LinDistCategory

class LinDistCategory (C : Type u) [Category.{v} C] (M : TwoMonoidalStructures C) extends LinDistCategoryStruct C M where
  -- Naturality
  leftDist_naturality :
    ∀ {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃),
      (f₁ ⊗ₘ[M] (f₂ ⅋ₘ[M] f₃)) ≫ δₗ[M] Y₁ Y₂ Y₃ = δₗ[M] X₁ X₂ X₃ ≫ ((f₁ ⊗ₘ[M] f₂) ⅋ₘ[M] f₃) := by cat_disch
  rightDist_naturality :
    ∀ {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃),
      ((f₁ ⅋ₘ[M] f₂) ⊗ₘ[M] f₃) ≫ δᵣ[M] Y₁ Y₂ Y₃ = δᵣ[M] X₁ X₂ X₃ ≫ (f₁ ⅋ₘ[M] (f₂ ⊗ₘ[M] f₃)) := by cat_disch
  -- Distributors and associativity
  pentagon1 :
    ∀ W X Y Z : C, (α⊗[M] W X (Y ⅋[M] Z)).hom ≫ (W ◁⊗[M] (δₗ[M] X Y Z)) ≫ δₗ[M] W (X ⊗[M] Y) Z = δₗ[M] (W ⊗[M] X) Y Z ≫ ((α⊗[M] W X Y).hom ▷⅋[M] Z) := by cat_disch
  pentagon2 :
    ∀ W X Y Z : C, (W ◁⊗[M] (α⅋[M] X Y Z).hom) ≫ δₗ[M] W X (Y ⅋[M] Z) = δₗ[M] W (X ⅋[M] Y) Z ≫ ((δₗ[M] W X Y) ▷⅋[M] Z) ≫ (α⅋[M] (W ⊗[M] X) Y Z).hom := by cat_disch
  pentagon3 :
    ∀ W X Y Z : C, (α⊗[M] (W ⅋[M] X) Y Z).hom ≫ δᵣ[M] W X (Y ⊗[M] Z) = ((δᵣ[M] W X Y) ▷⊗[M] Z) ≫ δᵣ[M] W (X ⊗[M] Y) Z ≫ (W ◁⅋[M] (α⊗[M] X Y Z).hom) := by cat_disch
  pentagon4 :
    ∀ W X Y Z : C, (δᵣ[M] (W ⅋[M] X) Y Z) ≫ (α⅋[M] W X (Y ⊗[M] Z)).hom = ((α⅋[M] W X Y).hom ▷⊗[M] Z) ≫ (δᵣ[M] W (X ⅋[M] Y) Z) ≫ (W ◁⅋[M] (δᵣ[M] X Y Z)) := by cat_disch
  -- Distributors and units
  triangle1 :
    ∀ X Y : C, (λ⊗[M] (X ⅋[M] Y)).hom = (δₗ[M] (𝟙⊗[M]) X Y) ≫ ((λ⊗[M] X).hom ▷⅋[M] Y) := by cat_disch
  triangle2 :
    ∀ X Y : C, (ρ⊗[M] (X ⅋[M] Y)).hom = (δᵣ[M] X Y (𝟙⊗[M])) ≫ X ◁⅋[M] ((ρ⊗[M] Y).hom) := by cat_disch
  triangle3:
    ∀ X Y : C, ((λ⅋[M] X).hom ▷⊗[M] Y) = (δᵣ[M] (𝟙⅋[M]) X Y) ≫ (λ⅋[M] (X ⊗[M] Y)).hom := by cat_disch
  triangle4:
    ∀ X Y : C, (X ◁⊗[M] (ρ⅋[M] Y).hom) = (δₗ[M] X Y (𝟙⅋[M])) ≫ (ρ⅋[M] (X ⊗[M] Y)).hom := by cat_disch
  -- Distributors and distributors
  pentagon5 :
    ∀ W X Y Z : C, δₗ[M] (W ⅋[M] X) Y Z ≫ ((δᵣ[M] W X Y) ▷⅋[M] Z) ≫ (α⅋[M] W (X ⊗[M] Y) Z).hom = δᵣ[M] W X (Y ⅋[M] Z) ≫ (W ◁⅋[M] δₗ[M] X Y Z) := by cat_disch
  pentagon6 :
    ∀ W X Y Z : C, (α⊗[M] W (X ⅋[M] Y) Z).hom ≫ (W ◁⊗[M] δᵣ[M] X Y Z) ≫ δₗ[M] W X (Y ⊗[M] Z) = (δₗ[M] W X Y ▷⊗[M] Z) ≫ δᵣ[M] (W ⊗[M] X) Y Z := by cat_disch

attribute [reassoc] LinDistCategory.leftDist_naturality
attribute [reassoc] LinDistCategory.rightDist_naturality
attribute [reassoc (attr := simp)] LinDistCategory.pentagon1
attribute [reassoc (attr := simp)] LinDistCategory.pentagon2
attribute [reassoc (attr := simp)] LinDistCategory.pentagon3
attribute [reassoc (attr := simp)] LinDistCategory.pentagon4
attribute [reassoc (attr := simp)] LinDistCategory.pentagon5
attribute [reassoc (attr := simp)] LinDistCategory.pentagon6
attribute [reassoc (attr := simp)] LinDistCategory.triangle1
attribute [reassoc (attr := simp)] LinDistCategory.triangle2
attribute [reassoc (attr := simp)] LinDistCategory.triangle3
attribute [reassoc (attr := simp)] LinDistCategory.triangle4


class MixCategory (C : Type u) [Category.{v} C] (M : TwoMonoidalStructures C) extends LinDistCategory C M where
  mixator : 𝟙⅋[M] ⟶ 𝟙⊗[M]
  octagon : ∀ X Y : C, (X ◁⊗[M] (λ⅋[M] Y).inv) ≫ (X ◁⊗[M] (mixator ▷⅋[M] Y)) ≫ (δₗ[M] X (𝟙⊗[M]) Y) ≫ ((ρ⊗[M] X).hom ▷⅋[M] Y) = ((ρ⅋[M] X).inv ▷⊗[M] Y) ≫ ((X ◁⅋[M] mixator) ▷⊗[M] Y) ≫ (δᵣ[M] X (𝟙⊗[M]) Y) ≫ (X ◁⅋[M] (λ⊗[M] Y).hom)

open MonoidalCategory
namespace LinDistCategory

variable (C : Type u) [Category.{v} C] (M : TwoMonoidalStructures C) [LinDistCategory C M]

@[reassoc]
theorem leftDist_naturality_left {X₁ Y₁ : C} (f : X₁ ⟶ Y₁) (X₂ X₃ : C) :
  (f ▷⊗[M] (X₂ ⅋[M] X₃)) ≫ (δₗ[M] Y₁ X₂ X₃) = (δₗ[M] X₁ X₂ X₃) ≫ (f ▷⊗[M] X₂) ▷⅋[M] X₃ := by
    simp [← tensorHom_id, ← leftDist_naturality]

@[reassoc]
theorem leftDist_naturality_middle {X₂ Y₂ : C} (f : X₂ ⟶ Y₂) (X₁ X₃ : C) :
  (X₁ ◁⊗[M] (f ▷⅋[M] X₃)) ≫ (δₗ[M] X₁ Y₂ X₃) = (δₗ[M] X₁ X₂ X₃) ≫ (X₁ ◁⊗[M] f) ▷⅋[M] X₃ := by
    simp [← tensorHom_id, ← id_tensorHom, ← leftDist_naturality]

@[reassoc]
theorem leftDist_naturality_right {X₃ Y₃ : C} (f : X₃ ⟶ Y₃) (X₁ X₂ : C) :
  (X₁ ◁⊗[M] (X₂ ◁⅋[M] f)) ≫ (δₗ[M] X₁ X₂ Y₃) = (δₗ[M] X₁ X₂ X₃) ≫ (X₁ ⊗[M] X₂) ◁⅋[M] f := by
    simp [← id_tensorHom, leftDist_naturality]

@[reassoc]
theorem rightDist_naturality_left {X₁ Y₁ : C} (f : X₁ ⟶ Y₁) (X₂ X₃ : C) :
  ((f ▷⅋[M] X₂) ▷⊗[M] X₃) ≫ (δᵣ[M] Y₁ X₂ X₃) = (δᵣ[M] X₁ X₂ X₃) ≫ (f ▷⅋[M] (X₂ ⊗[M] X₃)) := by
    simp [← tensorHom_id, rightDist_naturality]

@[reassoc]
theorem rightDist_naturality_middle {X₂ Y₂ : C} (f : X₂ ⟶ Y₂) (X₁ X₃ : C) :
  ((X₁ ◁⅋[M] f) ▷⊗[M] X₃) ≫ (δᵣ[M] X₁ Y₂ X₃) = (δᵣ[M] X₁ X₂ X₃) ≫ (X₁ ◁⅋[M] (f ▷⊗[M] X₃)) := by
    simp [← tensorHom_id, ← id_tensorHom, ← rightDist_naturality]

@[reassoc]
theorem rightDist_naturality_right {X₃ Y₃ : C} (f : X₃ ⟶ Y₃) (X₁ X₂ : C) :
  ((X₁ ⅋[M] X₂) ◁⊗[M] f) ≫ (δᵣ[M] X₁ X₂ Y₃) = (δᵣ[M] X₁ X₂ X₃) ≫ (X₁ ◁⅋[M] (X₂ ◁⊗[M] f)) := by
    simp [← id_tensorHom, ← rightDist_naturality]

end LinDistCategory
end CategoryTheory
