import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.CategoryTheory.Monoidal.Comon_
import TwoMonoidal.Basic

set_option linter.style.header false
set_option linter.style.longLine false

namespace CategoryTheory
namespace DuoidalCategory

scoped notation:70 X:71 " ⊗[" M "] " Y:71 =>
  TwoMonoidalStructures.tensorObj₁ M X Y

scoped notation:70 X:71 " ≺[" M "] " Y:71 =>
  TwoMonoidalStructures.tensorObj₂ M X Y

scoped notation:max " 𝟙⊗[" M "] " =>
  TwoMonoidalStructures.tensorUnit₁ M

scoped notation:max " 𝟙≺[" M "] " =>
  TwoMonoidalStructures.tensorUnit₂ M

scoped notation:70 f:71 " ⊗ₘ[" M "] " g:71 =>
  TwoMonoidalStructures.tensorHom₁ M f g

scoped notation:70 f:71 " ≺ₘ[" M "] " g:71 =>
  TwoMonoidalStructures.tensorHom₂ M f g

scoped notation "α⊗[" M "]" =>
  TwoMonoidalStructures.tensorAssociator₁ M

scoped notation "α≺[" M "]" =>
  TwoMonoidalStructures.tensorAssociator₂ M

scoped notation:70 X:71 "◁⊗[" M "]" f:71 =>
  TwoMonoidalStructures.tensorwhiskerLeft₁ M X f

scoped notation:70 f:71 "▷⊗[" M "]" Y:71 =>
  TwoMonoidalStructures.tensorwhiskerRight₁ M Y f

scoped notation:70 X:71 "◁≺[" M "]" f:71 =>
  TwoMonoidalStructures.tensorwhiskerLeft₂ M X f

scoped notation:70 f:71 "▷≺[" M "]" Y:71 =>
  TwoMonoidalStructures.tensorwhiskerRight₂ M Y f

scoped notation "ρ⊗[" M "]" =>
  TwoMonoidalStructures.tensorrightUnitor₁ M

scoped notation "λ⊗[" M "]" =>
  TwoMonoidalStructures.tensorleftUnitor₁ M

scoped notation "ρ≺[" M "]" =>
  TwoMonoidalStructures.tensorrightUnitor₂ M

scoped notation "λ≺[" M "]" =>
  TwoMonoidalStructures.tensorleftUnitor₂ M

end DuoidalCategory

open DuoidalCategory

-- Underlying structure of duoidal cats
class DuoidalCategoryStruct (C : Type u) [Category.{v} C] (M : TwoMonoidalStructures C) where
  distributor : ∀ W X Y Z : C, (W ≺[M] X) ⊗[M] (Y ≺[M] Z) ⟶ (W ⊗[M] Y) ≺[M] (X ⊗[M] Z)
  tensorUnitcomult : 𝟙⊗[M] ⟶ 𝟙⊗[M] ≺[M] 𝟙⊗[M]
  seqUnitmult : 𝟙≺[M] ⊗[M] 𝟙≺[M] ⟶ 𝟙≺[M]
  tensorUnitseq : 𝟙⊗[M] ⟶ 𝟙≺[M]

namespace DuoidalCategory

scoped notation "δ[" M "]" =>
  DuoidalCategoryStruct.distributor (M := M)

scoped notation "γ[" M "]" =>
  DuoidalCategoryStruct.tensorUnitcomult (M := M)

scoped notation "μ[" M "]" =>
  DuoidalCategoryStruct.seqUnitmult (M := M)

scoped notation "ν[" M "]" =>
  DuoidalCategoryStruct.tensorUnitseq (M := M)

end DuoidalCategory

class DuoidalCategory (C : Type u) [Category.{v} C] (M : TwoMonoidalStructures C) extends DuoidalCategoryStruct C M where
-- Naturality
  Dist_naturality :
    ∀ {X₁ X₂ X₃ X₄ Y₁ Y₂ Y₃ Y₄ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) (f₄ : X₄ ⟶ Y₄),
      ((f₁ ≺ₘ[M] f₂) ⊗ₘ[M] (f₃ ≺ₘ[M] f₄)) ≫ δ[M] Y₁ Y₂ Y₃ Y₄ = δ[M] X₁ X₂ X₃ X₄ ≫ ((f₁ ⊗ₘ[M] f₃) ≺ₘ[M] (f₂ ⊗ₘ[M] f₄))
  tensorAssociatorHexagon :
    ∀ U V W X Y Z : C, ((δ[M] U V W X) ▷⊗[M] (Y ≺[M] Z)) ≫ δ[M] (U ⊗[M] W) (V ⊗[M] X) Y Z ≫ ((α⊗[M] U W Y).hom ≺ₘ[M] (α⊗[M] V X Z).hom) = (α⊗[M] (U ≺[M] V) (W ≺[M] X) (Y ≺[M] Z)).hom ≫ ((U ≺[M] V) ◁⊗[M] (δ[M] W X Y Z)) ≫ (δ[M] U V (W ⊗[M] Y) (X ⊗[M] Z))
  seqAssociatorHexagon :
    ∀ U V W X Y Z : C, δ[M] (U ≺[M] V) W (X ≺[M] Y) Z ≫ ((δ[M] U V X Y) ▷≺[M] (W ⊗[M] Z)) ≫ (α≺[M] (U ⊗[M] X) (V ⊗[M] Y) (W ⊗[M] Z)).hom = ((α≺[M] U V W).hom ⊗ₘ[M] (α≺[M] X Y Z).hom) ≫ (δ[M] U (V ≺[M] W) X (Y ≺[M] Z)) ≫ ((U ⊗[M] X) ◁≺[M] δ[M] V W Y Z)
  tensorleftUnitorSquare :
    ∀ X Y : C, (γ[M] ▷⊗[M] (X ≺[M] Y)) ≫ (δ[M] 𝟙⊗[M] 𝟙⊗[M] X Y) ≫ ((λ⊗[M] X).hom ≺ₘ[M] (λ⊗[M] Y).hom) = (λ⊗[M] (X ≺[M] Y)).hom
  tensorrightUnitorSquare :
    ∀ X Y : C, ((X ≺[M] Y) ◁⊗[M] γ[M]) ≫ (δ[M] X Y 𝟙⊗[M] 𝟙⊗[M]) ≫ ((ρ⊗[M] X).hom ≺ₘ[M] (ρ⊗[M] Y).hom) = (ρ⊗[M] (X ≺[M] Y)).hom
  seqleftUnitorSquare :
    ∀ X Y : C, δ[M] 𝟙≺[M] X 𝟙≺[M] Y ≫ (μ[M] ▷≺[M] (X ⊗[M] Y)) ≫ (λ≺[M] (X ⊗[M] Y)).hom = (λ≺[M] X).hom ⊗ₘ[M] (λ≺[M] Y).hom
  seqrightUnitorSquare :
    ∀ X Y : C, δ[M] X 𝟙≺[M] Y 𝟙≺[M] ≫ ((X ⊗[M] Y) ◁≺[M] μ[M]) ≫ (ρ≺[M] (X ⊗[M] Y)).hom = (ρ≺[M] X).hom ⊗ₘ[M] (ρ≺[M] Y).hom
  muAssociativity :
    (μ[M] ▷⊗[M] 𝟙≺[M]) ≫ μ[M] = (α⊗[M] 𝟙≺[M] 𝟙≺[M] 𝟙≺[M]).hom ≫ (𝟙≺[M] ◁⊗[M] μ[M]) ≫ μ[M]
  murightUnit :
    (𝟙≺[M] ◁⊗[M] ν[M]) ≫ μ[M] = (ρ⊗[M] 𝟙≺[M]).hom
  muleftUnit :
    (ν[M] ▷⊗[M] 𝟙≺[M]) ≫ μ[M] = (λ⊗[M] 𝟙≺[M]).hom
  gammaCoassociativity :
    γ[M] ≫ (𝟙⊗[M] ◁≺[M] γ[M]) = γ[M] ≫ (γ[M] ▷≺[M] 𝟙⊗[M]) ≫ (α≺[M] 𝟙⊗[M] 𝟙⊗[M] 𝟙⊗[M]).hom
  gammarightCounit :
    γ[M] ≫ (𝟙⊗[M] ◁≺[M] ν[M]) = (ρ≺[M] 𝟙⊗[M]).inv
  gammaleftCounit :
    γ[M] ≫ (ν[M] ▷≺[M] 𝟙⊗[M]) = (λ≺[M] 𝟙⊗[M]).inv



variable {C : Type u} [Category.{v} C]
variable {M : TwoMonoidalStructures C}

def seqUnitMonObj
    [D : DuoidalCategory C M] :
    @MonObj C _ M.tensor₁ (𝟙≺[M]) := by
  letI : MonoidalCategory C := M.tensor₁
  exact
    { one := ν[M]
      mul := μ[M]
      one_mul := D.muleftUnit
      mul_one := D.murightUnit
      mul_assoc := D.muAssociativity }

def tensorUnitComonObj
    [D : DuoidalCategory C M] :
    @ComonObj C _ M.tensor₂ (𝟙⊗[M]) := by
  letI : MonoidalCategory C := M.tensor₂
  exact
    { counit := ν[M]
      comul := γ[M]
      counit_comul := D.gammaleftCounit
      comul_counit := D.gammarightCounit
      comul_assoc := D.gammaCoassociativity }

@[simp]
theorem seqUnitMonObj_one
    [DuoidalCategory C M] :
    @MonObj.one C _ M.tensor₁ (𝟙≺[M]) (seqUnitMonObj) =
      ν[M] :=
  rfl

@[simp]
theorem seqUnitMonObj_mul
    [DuoidalCategory C M] :
    @MonObj.mul C _ M.tensor₁ (𝟙≺[M]) (seqUnitMonObj) =
      μ[M] :=
  rfl

@[simp]
theorem tensorUnitMonObj_one
    [DuoidalCategory C M] :
    @ComonObj.counit C _ M.tensor₂ (𝟙⊗[M]) (tensorUnitComonObj) =
      ν[M] :=
  rfl

@[simp]
theorem tensorUnitMonObj_mul
    [DuoidalCategory C M] :
    @ComonObj.comul C _ M.tensor₂ (𝟙⊗[M]) (tensorUnitComonObj) =
      γ[M] :=
  rfl

end CategoryTheory
