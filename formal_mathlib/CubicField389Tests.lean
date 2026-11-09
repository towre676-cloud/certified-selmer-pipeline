import CubicField389

namespace CertifiedSelmer.Mathlib389.CubicField
open CertifiedSelmer.FullDescent389

example : Algebra.norm ℚ (encode pi) = -2 := by
  rw [norm_encode, norm_pi]
  norm_num

example : Algebra.norm ℚ (encode unitP) = 1 ∧ Algebra.norm ℚ (encode unitQ) = 1 := by
  rw [norm_encode, norm_encode, norm_unitP, norm_unitQ]
  norm_num

example : encode pi ^ 4 * encode unitP = encode alphaP := by
  have h := congrArg encode normalize_P
  simpa [FullDescent389.sq, encode_mul, pow_succ, mul_assoc] using h

example : ∃ z : K, encode alphaP * z ^ 2 = -theta := by
  simpa using (lift_cover cover_P).2

example : ∃ z : K, encode (mul alphaP alphaQ) * z ^ 2 = -8 - theta := by
  simpa using (lift_cover cover_product).2

end CertifiedSelmer.Mathlib389.CubicField
