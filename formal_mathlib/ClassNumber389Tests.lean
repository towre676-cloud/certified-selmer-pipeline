import ClassNumber389

namespace CertifiedSelmer.Mathlib389.CubicField

open NumberField NumberField.InfinitePlace
open scoped NumberField

example : nrRealPlaces K = 3 ∧ nrComplexPlaces K = 0 := field_signature

example : Algebra.norm ℤ (betaInteger - 1) = -2 := by
  rw [← Int.cast_one, norm_betaInteger_sub]
  decide

example : Algebra.norm ℤ (betaInteger - 2) = 3 := by
  rw [← Int.cast_ofNat, norm_betaInteger_sub]
  decide

example (P : Ideal (𝓞 K)) (hP : P.IsPrime) (h2 : (2 : 𝓞 K) ∈ P) :
    Ideal.absNorm P = 2 := by
  rw [prime_over_two P hP h2, absNorm_betaInteger_sub_one]

example : NumberField.classNumber K = 1 := class_number

end CertifiedSelmer.Mathlib389.CubicField
