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


def shifted_tensor
  [tensor_inverse_pair J] :
  @MonoidalCategory C _ := by
  exact
    {
      tensorObj X Y := X ⊗ (J^ ⊗ Y)
      whiskerLeft (X : C) {Y₁ Y₂ : C} (f : Y₁ ⟶ Y₂) := X ◁ (J^ ◁ f)
      whiskerRight {X₁ X₂ : C} (f : X₁ ⟶ X₂) (Y : C) := f ▷ (J^ ⊗ Y)
      tensorUnit := J
      associator X Y Z := (α_ X (J^ ⊗ Y) (J^ ⊗ Z)) ≪≫ (X ◁ᵢ (α_ J^ Y (J^ ⊗ Z)))
      leftUnitor X := (α_ J J^ X).symm ≪≫ (sₗ[J] ▷ᵢ X) ≪≫ λ_ X
      rightUnitor X := (X ◁ᵢ sᵣ[J]) ≪≫ ρ_ X
      tensorHom_comp_tensorHom := by
        intro X₁ Y₁ Z₁ X₂ Y₂ Z₂ f₁ f₂ g₁ g₂
        dsimp
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



end CategoryTheory
