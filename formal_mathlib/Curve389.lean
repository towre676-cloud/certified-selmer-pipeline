import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

noncomputable section

namespace CertifiedSelmer.Mathlib389
open Polynomial

/-- The actual rational Weierstrass curve, not a receipt label. -/
def E : WeierstrassCurve ℚ := ⟨0, 1, 1, -2, 0⟩

def divisionCubic : ℤ[X] := X^3 + C 4 * X^2 + C (-32) * X + C 16

lemma divisionCubic_monic : divisionCubic.Monic := by
  apply monic_of_natDegree_le_of_coeff_eq_one 3
  · dsimp [divisionCubic]
    compute_degree
  · norm_num [divisionCubic, Polynomial.coeff_X]

lemma divisionCubic_no_rat_root (r : ℚ) : aeval r divisionCubic ≠ 0 := by
  intro hr
  obtain ⟨z, hz⟩ := isInteger_of_is_root_of_monic divisionCubic_monic hr
  have hr' : r^3 + 4*r^2 + (-32)*r + 16 = 0 := by
    simpa [divisionCubic, Polynomial.aeval_def] using hr
  change (z : ℚ) = r at hz
  have hi : z^3 + 4*z^2 + (-32)*z + 16 = (0 : ℤ) := by
    rw [← hz] at hr'
    exact_mod_cast hr'
  have hm := congrArg (Int.castRingHom (ZMod 5)) hi
  norm_num [map_add, map_mul, map_pow] at hm
  have h32 : (32 : ZMod 5) = 2 := by decide
  have h16 : (16 : ZMod 5) = 1 := by decide
  rw [h32, h16] at hm
  have hneg : (-2 : ZMod 5) = 3 := by decide
  have hm' : (z : ZMod 5)^3 + 4*(z : ZMod 5)^2 + 3*(z : ZMod 5) + 1 = 0 := by
    calc
      _ = (z : ZMod 5)^3 + 4*(z : ZMod 5)^2 - 2*(z : ZMod 5) + 1 := by
        rw [sub_eq_add_neg, ← neg_mul, hneg]
      _ = 0 := by linear_combination hm
  have hn : ∀ a : ZMod 5, a^3 + 4*a^2 + 3*a + 1 ≠ 0 := by decide
  exact hn (z : ZMod 5) hm'

/-- A curve-level fact: no rational affine point is fixed by negation. -/
lemma affine_not_two_torsion {x y : ℚ} (h : E.toAffine.Equation x y) :
    2*y + 1 ≠ 0 := by
  intro hy
  have he : y^2 + y = x^3 + x^2 - 2*x := by
    simpa [E, sub_eq_add_neg] using (WeierstrassCurve.Affine.equation_iff x y).mp h
  apply divisionCubic_no_rat_root (4*x)
  simp only [divisionCubic, map_add, map_mul, map_pow, aeval_X, aeval_C]
  norm_num
  nlinarith [sq_nonneg (2*y+1)]

lemma discriminant_eq : E.Δ = 389 := by
  norm_num [E, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

instance elliptic : E.IsElliptic := ⟨by rw [discriminant_eq]; norm_num⟩

lemma two_torsion_trivial (P : E.toAffine.Point) (h : 2 • P = 0) : P = 0 := by
  have heq : P = -P := eq_neg_of_add_eq_zero_left (by simpa [two_nsmul] using h)
  cases P with
  | zero => rfl
  | @some x y hns =>
      rw [WeierstrassCurve.Affine.Point.neg_some] at heq
      have hy := (WeierstrassCurve.Affine.Point.some.inj heq).2
      have hn := affine_not_two_torsion hns.1
      apply False.elim
      apply hn
      simp only [E, WeierstrassCurve.Affine.negY] at hy
      linarith

lemma two_power_torsion_trivial (n : ℕ) (P : E.toAffine.Point)
    (h : (2^n) • P = 0) : P = 0 := by
  induction n generalizing P with
  | zero => simpa using h
  | succ n ih =>
      apply ih P
      apply two_torsion_trivial ((2^n) • P)
      simpa only [pow_succ, mul_nsmul] using h

end CertifiedSelmer.Mathlib389
