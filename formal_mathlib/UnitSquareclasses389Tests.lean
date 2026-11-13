import UnitSquareclasses389

namespace CertifiedSelmer.Mathlib389.CubicField
open NumberField
open scoped NumberField

example : NumberField.Units.rank K = 2 := unit_rank

example : Module.finrank (ZMod 2) (Additive squareclassNorm.ker) = 2 :=
  norm_square_kernel_finrank

example : Nat.card squareclassNorm.ker = 4 := norm_square_kernel_card

example : explicitNormSquareClasses 0 = 1 := rfl
example : explicitNormSquareClasses 1 = classP := rfl
example : explicitNormSquareClasses 2 = classQ := rfl
example : explicitNormSquareClasses 3 = classP * classQ := rfl

example : ¬ IsSquare ((descentUnitP : K) * (descentUnitQ : K)) :=
  descentUnitProduct_nonsquare

end CertifiedSelmer.Mathlib389.CubicField
