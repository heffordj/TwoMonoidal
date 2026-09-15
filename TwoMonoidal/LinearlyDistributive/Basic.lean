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

scoped notation:71 " 𝟙⊗[" M "] " =>
  TwoMonoidalStructures.tensorUnit₁ M

scoped notation:71 " 𝟙⅋[" M "] " =>
  TwoMonoidalStructures.tensorUnit₂ M

scoped notation:70 f " ⊗ₘ[" M "] " g =>
  TwoMonoidalStructures.tensorHom₁ M f g

scoped notation:70 f " ⅋ₘ[" M "] " g =>
  TwoMonoidalStructures.tensorHom₂ M f g

scoped notation "α⊗[" M "]" =>
  TwoMonoidalStructures.tensorAssociator₁ M

scoped notation "α⅋[" M "]" =>
  TwoMonoidalStructures.tensorAssociator₂ M

scoped notation X "◁⊗[" M "]" f =>
  TwoMonoidalStructures.tensorwhiskerLeft₁ M X f

scoped notation f "▷⊗[" M "]" Y =>
  TwoMonoidalStructures.tensorwhiskerRight₁ M Y f

scoped notation X "◁⅋[" M "]" f =>
  TwoMonoidalStructures.tensorwhiskerLeft₂ M X f

scoped notation f "▷⅋[" M "]" Y =>
  TwoMonoidalStructures.tensorwhiskerRight₂ M Y f

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
      (f₁ ⊗ₘ[M] (f₂ ⅋ₘ[M] f₃)) ≫ δₗ[M] Y₁ Y₂ Y₃ = δₗ[M] X₁ X₂ X₃ ≫ ((f₁ ⊗ₘ[M] f₂) ⅋ₘ[M] f₃)
  rightDist_naturality :
    ∀ {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃),
      ((f₁ ⅋ₘ[M] f₂) ⊗ₘ[M] f₃) ≫ δᵣ[M] Y₁ Y₂ Y₃ = δᵣ[M] X₁ X₂ X₃ ≫ (f₁ ⅋ₘ[M] (f₂ ⊗ₘ[M] f₃))
  -- Distributors and associativity
  pentagon1 :
    ∀ W X Y Z : C, (α⊗[M] W X (Y ⅋[M] Z)).hom ≫ (W ◁⊗[M] (δₗ[M] X Y Z)) ≫ δₗ[M] W (X ⊗[M] Y) Z = δₗ[M] (W ⊗[M] X) Y Z ≫ ((α⊗[M] W X Y).hom ▷⅋[M] Z)
  pentagon2 :
    ∀ W X Y Z : C, (W ◁⊗[M] (α⅋[M] X Y Z).hom) ≫ δₗ[M] W X (Y ⅋[M] Z) = δₗ[M] W (X ⅋[M] Y) Z ≫ ((δₗ[M] W X Y) ▷⅋[M] Z) ≫ (α⅋[M] (W ⊗[M] X) Y Z).hom
  pentagon3 :
    ∀ W X Y Z : C, (α⊗[M] (W ⅋[M] X) Y Z).hom ≫ δᵣ[M] W X (Y ⊗[M] Z) = ((δᵣ[M] W X Y) ▷⊗[M] Z) ≫ δᵣ[M] W (X ⊗[M] Y) Z ≫ (W ◁⅋[M] (α⊗[M] X Y Z).hom)
  pentagon4 :
    ∀ W X Y Z : C, (δᵣ[M] (W ⅋[M] X) Y Z) ≫ (α⅋[M] W X (Y ⊗[M] Z)).hom = ((α⅋[M] W X Y).hom ▷⊗[M] Z) ≫ (δᵣ[M] W (X ⅋[M] Y) Z) ≫ (W ◁⅋[M] (δᵣ[M] X Y Z))
  -- Distributors and units
  triangle1 :
    ∀ X Y : C, (λ⊗[M] (X ⅋[M] Y)).hom = (δₗ[M] (𝟙⊗[M]) X Y) ≫ ((λ⊗[M] X).hom ▷⅋[M] Y)
  triangle2 :
    ∀ X Y : C, (ρ⊗[M] (X ⅋[M] Y)).hom = (δᵣ[M] X Y (𝟙⊗[M])) ≫ X ◁⅋[M] ((ρ⊗[M] Y).hom)
  triangle3:
    ∀ X Y : C, ((λ⅋[M] X).hom ▷⊗[M] Y) = (δᵣ[M] (𝟙⅋[M]) X Y) ≫ (λ⅋[M] (X ⊗[M] Y)).hom
  triangle4:
    ∀ X Y : C, (X ◁⊗[M] (ρ⅋[M] Y).hom) = (δₗ[M] X Y (𝟙⅋[M])) ≫ (ρ⅋[M] (X ⊗[M] Y)).hom
  -- Distributors and distributors
  pentagon5 :
    ∀ W X Y Z : C, δₗ[M] (W ⅋[M] X) Y Z ≫ ((δᵣ[M] W X Y) ▷⅋[M] Z) ≫ (α⅋[M] W (X ⊗[M] Y) Z).hom = δᵣ[M] W X (Y ⅋[M] Z) ≫ (W ◁⅋[M] δₗ[M] X Y Z)
  pentagon6 :
    ∀ W X Y Z : C, (α⊗[M] W (X ⅋[M] Y) Z).hom ≫ (W ◁⊗[M] δᵣ[M] X Y Z) ≫ δₗ[M] W X (Y ⊗[M] Z) = (δₗ[M] W X Y ▷⊗[M] Z) ≫ δᵣ[M] (W ⊗[M] X) Y Z


class MixCategory (C : Type u) [Category.{v} C] (M : TwoMonoidalStructures C) extends LinDistCategory C M where
  mixator : 𝟙⅋[M] ⟶ 𝟙⊗[M]
  octagon : ∀ X Y : C, (X ◁⊗[M] (λ⅋[M] Y).inv) ≫ (X ◁⊗[M] (mixator ▷⅋[M] Y)) ≫ (δₗ[M] X (𝟙⊗[M]) Y) ≫ ((ρ⊗[M] X).hom ▷⅋[M] Y) = ((ρ⅋[M] X).inv ▷⊗[M] Y) ≫ ((X ◁⅋[M] mixator) ▷⊗[M] Y) ≫ (δᵣ[M] X (𝟙⊗[M]) Y) ≫ (X ◁⅋[M] (λ⊗[M] Y).hom)

end CategoryTheory
