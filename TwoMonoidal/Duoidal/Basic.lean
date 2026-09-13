import Mathlib.CategoryTheory.Monoidal.Category
import TwoMonoidal.Basic

set_option linter.style.header false
set_option linter.style.longLine false

namespace CategoryTheory
namespace DuoidalCategory

scoped notation:70 X:71 " ⊗[" M "] " Y:71 =>
  TwoMonoidalStructures.tensorObj₁ M X Y

scoped notation:70 X:71 " ≺[" M "] " Y:71 =>
  TwoMonoidalStructures.tensorObj₂ M X Y

scoped notation:71 " 𝟙⊗[" M "] " =>
  TwoMonoidalStructures.tensorUnit₁ M

scoped notation:71 " 𝟙≺[" M "] " =>
  TwoMonoidalStructures.tensorUnit₂ M

scoped notation:70 f " ⊗ₘ[" M "] " g =>
  TwoMonoidalStructures.tensorHom₁ M f g

scoped notation:70 f " ≺ₘ[" M "] " g =>
  TwoMonoidalStructures.tensorHom₂ M f g

scoped notation "α⊗[" M "]" =>
  TwoMonoidalStructures.tensorAssociator₁ M

scoped notation "α≺[" M "]" =>
  TwoMonoidalStructures.tensorAssociator₂ M

scoped notation X "◁⊗[" M "]" f =>
  TwoMonoidalStructures.tensorwhiskerLeft₁ M X f

scoped notation f "▷⊗[" M "]" Y =>
  TwoMonoidalStructures.tensorwhiskerRight₁ M Y f

scoped notation X "◁≺[" M "]" f =>
  TwoMonoidalStructures.tensorwhiskerLeft₂ M X f

scoped notation f "▷≺[" M "]" Y =>
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

end CategoryTheory
