import Mathlib.CategoryTheory.Monoidal.Category
import TwoMonoidal.LinearlyDistributive.Basic

set_option linter.style.header false
set_option linter.style.longLine false

open CategoryTheory.LinDistCategory
namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {M : TwoMonoidalStructures C} [LinDistCategory C M]

class DualPair (X Y : C) where
  evaluation : X ⊗[M] Y ⟶ 𝟙⅋[M]
  coevaluation : 𝟙⊗[M] ⟶ Y ⅋[M] X
  snake1 : (X ◁⊗[M] coevaluation) ≫ (δₗ[M] _ _ _) ≫ (evaluation ▷⅋[M] X) ≫ (λ⅋[M] _).hom = (ρ⊗[M] _).hom := by cat_disch
  snake2 : (coevaluation ▷⊗[M] Y) ≫ (δᵣ[M] _ _ _) ≫ (Y ◁⅋[M] evaluation) ≫ (ρ⅋[M] _).hom = (λ⊗[M] _).hom := by cat_disch

namespace DualPair

scoped notation "ε" =>
  DualPair.evaluation

scoped notation "η" =>
  DualPair.coevaluation

end DualPair

class HasRightDual (X : C) where
  rightDual : C
  [exact : DualPair (M := M) X rightDual]

class HasLeftDual (Y : C) where
  leftDual : C
  [exact : DualPair (M := M) leftDual Y]

class StarAutCategory (C : Type u) [Category.{v} C] {M : TwoMonoidalStructures C} extends LinDistCategory C M where
  [rightDual : ∀ X : C, HasRightDual (M:=M) X]
  [leftDual : ∀ X : C, HasLeftDual (M:=M) X]

end CategoryTheory
