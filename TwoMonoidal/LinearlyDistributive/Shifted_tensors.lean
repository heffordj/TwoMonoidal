import TwoMonoidal.LinearlyDistributive.Basic
import Mathlib.Tactic.CategoryTheory.Monoidal.Basic

set_option linter.style.header false
set_option linter.style.longLine false

open CategoryTheory.MonoidalCategory
namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

class tensor_inverse_pair (J : C) where
  tensor_inverse : C
  mul_left : J ⊗ tensor_inverse ≅ 𝟙_ C
  mul_right : tensor_inverse ⊗ J ≅ 𝟙_ C
  pentagon : (mul_right.hom ▷ tensor_inverse) ≫ (λ_ tensor_inverse).hom = (α_ tensor_inverse J tensor_inverse).hom ≫ (tensor_inverse ◁ mul_left.hom) ≫ (ρ_ tensor_inverse).hom

scoped notation:max J"^" => tensor_inverse_pair.tensor_inverse J
scoped notation:max "sₗ[" J "]" => tensor_inverse_pair.mul_left (J := J)
scoped notation:max "sᵣ[" J "]" => tensor_inverse_pair.mul_right (J := J)

variable (J : C)

@[instance_reducible, simps]
def shifted_tensor
  [tensor_inverse_pair J] :
  MonoidalCategory C := by
  exact
    {
      tensorObj X Y := X ⊗ (J^ ⊗ Y)
      whiskerLeft (X : C) {Y₁ Y₂ : C} (f : Y₁ ⟶ Y₂) := X ◁ (J^ ◁ f)
      whiskerRight {X₁ X₂ : C} (f : X₁ ⟶ X₂) (Y : C) := f ▷ (J^ ⊗ Y)
      tensorHom {X₁ Y₁ X₂ Y₂} f g :=
      (f ▷ (J^ ⊗ X₂)) ≫
        (Y₁ ◁ (J^ ◁ g))
      tensorUnit := J
      associator X Y Z := (α_ X (J^ ⊗ Y) (J^ ⊗ Z)) ≪≫ (X ◁ᵢ (α_ J^ Y (J^ ⊗ Z)))
      leftUnitor X := (α_ J J^ X).symm ≪≫ (sₗ[J] ▷ᵢ X) ≪≫ λ_ X
      rightUnitor X := (X ◁ᵢ sᵣ[J]) ≪≫ ρ_ X
      tensorHom_comp_tensorHom := by
        intro X₁ Y₁ Z₁ X₂ Y₂ Z₂ f₁ f₂ g₁ g₂
        simp only [Category.assoc]
        rw [whisker_exchange_assoc]
        monoidal
      associator_naturality := by
        intro X₁ X₂ X₃ Y₁ Y₂ Y₃ f₁ f₂ f₃
        simp
        monoidal
      leftUnitor_naturality := by
        intro X₁ X₂ f
        simp only [Iso.trans_hom, Iso.symm_hom, whiskerRightIso_hom, Category.assoc]
        rw [associator_inv_naturality_right_assoc]
        rw [whisker_exchange_assoc]
        monoidal
      rightUnitor_naturality := by
        intro X₁ X₂ f
        simp only [whiskerRight_tensor, Iso.trans_hom, whiskerLeftIso_hom, Category.assoc]
        rw [associator_naturality_left_assoc]
        rw [← whisker_exchange_assoc]
        monoidal
      pentagon := by
        intro W X Y Z
        simp
        monoidal
      triangle := by
        intro X Y
        dsimp
        rw [whiskerLeft_comp, whiskerLeft_comp J^]
        rw [← triangle_assoc_comp_right]
        rw [whiskerRightIso_hom]
        rw [associator_inv_naturality_middle_assoc]
        rw [whiskerLeftIso_hom]
        rw [Category.assoc]
        rw [← whiskerLeft_comp]
        rw [pentagon_hom_inv_inv_inv_hom_assoc]
        simp only [← comp_whiskerRight,← tensor_inverse_pair.pentagon]
        rw [comp_whiskerRight]
        rw [← associator_inv_naturality_left_assoc]
        rw [whiskerLeft_comp]
        rw [← associator_naturality_middle_assoc]
        simp
        monoidal
    }

open LinDistCategory

abbrev shifted_tensor_TwoMonoidalStructure
  [tensor_inverse_pair J] :
  TwoMonoidalStructures C := by
  exact
    { tensor₁ := inferInstance
      tensor₂ := shifted_tensor J
    }

-- @[simp]
-- theorem shifted_tensorObj₁
--   [tensor_inverse_pair J] (X Y : C) :
--   X ⊗[shifted_tensor_TwoMonoidalStructure J] Y =
--     X ⊗ Y := rfl

-- @[reassoc (attr := simp)]
-- theorem shifted_tensorHom₁
--   [tensor_inverse_pair J]
--   {X₁ Y₁ X₂ Y₂ : C}
--   (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
--   f ⊗ₘ[shifted_tensor_TwoMonoidalStructure J] g =
--     f ⊗ₘ g := rfl

-- @[simp]
-- theorem shifted_tensorObj₂
--   [tensor_inverse_pair J] (X Y : C) :
--   X ⅋[shifted_tensor_TwoMonoidalStructure J] Y =
--     X ⊗ (J^ ⊗ Y) := rfl

-- @[reassoc (attr := simp)]
-- theorem shifted_tensorHom₂
--   [tensor_inverse_pair J]
--   {X₁ Y₁ X₂ Y₂ : C}
--   (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
--   f ⅋ₘ[shifted_tensor_TwoMonoidalStructure J] g =
--     (f ▷ (J^ ⊗ X₂)) ≫ Y₁ ◁ (J^ ◁ g) := rfl

-- @[reassoc (attr := simp)]
-- theorem shifted_tensorAssoc₁
--   [tensor_inverse_pair J] (X Y Z : C) :
--   α⊗[shifted_tensor_TwoMonoidalStructure J] X Y Z = α_ X Y Z := rfl

-- @[reassoc (attr := simp)]
-- theorem shifted_tensorAssoc₂
--   [tensor_inverse_pair J] (X Y Z : C) :
--   α⅋[shifted_tensor_TwoMonoidalStructure J] X Y Z = (shifted_tensor J).associator X Y Z := rfl

-- @[reassoc (attr := simp)]
-- theorem shifted_tensorWhiskerleft₁
--   [tensor_inverse_pair J] (X : C) {Y₁ Y₂ : C} (f : Y₁ ⟶ Y₂) :
--   X ◁⊗[shifted_tensor_TwoMonoidalStructure J] f = X ◁ f := rfl

-- @[reassoc (attr := simp)]
-- theorem shifted_tensorWhiskerleft₂
--   [tensor_inverse_pair J] (X : C) {Y₁ Y₂ : C} (f : Y₁ ⟶ Y₂) :
--   X ◁⅋[shifted_tensor_TwoMonoidalStructure J] f =  X ◁ (J^ ◁ f) := rfl

-- @[reassoc (attr := simp)]
-- theorem shifted_tensorWhiskerright₁
--   [tensor_inverse_pair J] {X₁ X₂ : C} (Y : C) (f : X₁ ⟶ X₂) :
--   f ▷⊗[shifted_tensor_TwoMonoidalStructure J] Y = f ▷ Y := rfl

-- @[reassoc (attr := simp)]
-- theorem shifted_tensorWhiskerright₂
--   [tensor_inverse_pair J] {X₁ X₂ : C} (Y : C) (f : X₁ ⟶ X₂) :
--   f ▷⅋[shifted_tensor_TwoMonoidalStructure J] Y =  f ▷ (J^ ⊗ Y) := rfl

def shifted_tensor_lin_distributive_category
  [tensor_inverse_pair J] :
  LinDistCategory C (shifted_tensor_TwoMonoidalStructure J) := by
  exact {
    leftDistributor X Y Z := (α_ X Y (J^ ⊗ Z)).inv
    rightDistributor X Y Z := (α_ X (J^ ⊗ Y) Z).hom ≫ X ◁ (α_ J^ Y Z).hom
    leftDist_naturality := by
      intro X₁ X₂ X₃ Y₁ Y₂ Y₃ f₁ f₂ f₃
      simp [left_Distributor, tensorHom_def]
    rightDist_naturality := by
      intro X₁ X₂ X₃ Y₁ Y₂ Y₃ f₁ f₂ f₃
      simp [right_Distributor,tensorHom_def]
    pentagon1 := by
      intro W X Y Z
      simp [left_Distributor]
    pentagon2 := by
      intro W X Y Z
      simp [left_Distributor]
      monoidal
    pentagon3 := by
      intro W X Y Z
      simp [right_Distributor]
      monoidal
    pentagon4 := by
      intro W X Y Z
      simp [right_Distributor]
      monoidal
    triangle1 := by
      intro X Y
      simp [left_Distributor]
    triangle2 := by
      intro X Y
      simp [right_Distributor]
    triangle3 := by
      intro X Y
      simp [right_Distributor]
    triangle4 := by
      intro X Y
      simp [left_Distributor]
    pentagon5 := by
      intro W X Y Z
      simp [left_Distributor,right_Distributor]
      monoidal
    pentagon6 := by
      intro W X Y Z
      simp [left_Distributor,right_Distributor]
  }

class LinDistCategory_Iso (C : Type u) [Category.{v} C] (M : TwoMonoidalStructures C) extends LinDistCategory C M where
  leftDistributor_iso (X Y Z : C) : IsIso (leftDistributor X Y Z)
  rightDistributor_iso (X Y Z : C) : IsIso (rightDistributor X Y Z)

def shifted_tensor_lin_distributive_category_Iso
  [tensor_inverse_pair J] :
  LinDistCategory_Iso C (shifted_tensor_TwoMonoidalStructure J) := by
  exact {
    toLinDistCategory := shifted_tensor_lin_distributive_category J
    leftDistributor_iso := by
      intro X Y Z
      unfold LinDistCategoryStruct.leftDistributor
      unfold shifted_tensor_lin_distributive_category
      simp only [shifted_tensor_tensorObj]
      infer_instance
    rightDistributor_iso := by
      intro X Y Z
      unfold LinDistCategoryStruct.rightDistributor
      unfold shifted_tensor_lin_distributive_category
      simp only [shifted_tensor_tensorObj, isIso_comp_left_iff]
      infer_instance
  }

end CategoryTheory
