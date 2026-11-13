import CubicField389
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith

/-! The signature, small prime ideals, and class number of the 389a1 cubic field. -/

noncomputable section

namespace CertifiedSelmer.Mathlib389.CubicField

open NumberField NumberField.InfinitePlace Polynomial
open scoped NumberField Real

private def cubic {R : Type*} [Ring R] (x : R) : R :=
  x ^ 3 - x ^ 2 - 9 * x + 11

private theorem real_root (a b : ℝ) (hab : a ≤ b)
    (h : cubic a ≤ 0 ∧ 0 ≤ cubic b ∨ cubic b ≤ 0 ∧ 0 ≤ cubic a) :
    ∃ x ∈ Set.Icc a b, cubic x = 0 := by
  have hc : Continuous (cubic : ℝ → ℝ) := by unfold cubic; fun_prop
  rcases h with h | h
  · exact intermediate_value_Icc hab hc.continuousOn h
  · exact intermediate_value_Icc' hab hc.continuousOn h

private def realEmbedding (x : ℝ) (hx : cubic x = 0) :
    {φ : K →+* ℂ // ComplexEmbedding.IsReal φ} := by
  have h : aeval x g = 0 := by
    rw [g, aeval_map_algebraMap ℚ]
    simpa [gZ, cubic, map_ofNat] using hx
  refine ⟨Complex.ofRealHom.comp (AdjoinRoot.liftHom g x h).toRingHom, ?_⟩
  rw [ComplexEmbedding.isReal_iff]
  ext1 z
  exact Complex.conj_ofReal _

private theorem realEmbedding_beta (x : ℝ) (hx : cubic x = 0) :
    ((realEmbedding x hx : K →+* ℂ) beta).re = x := by
  simp [realEmbedding, beta, AdjoinRoot.liftHom_root]

theorem field_signature : nrRealPlaces K = 3 ∧ nrComplexPlaces K = 0 := by
  classical
  obtain ⟨a, ha, hga⟩ := real_root (-4) (-3) (by norm_num) (by norm_num [cubic])
  obtain ⟨b, hb, hgb⟩ := real_root 0 (3 / 2) (by norm_num) (by norm_num [cubic])
  obtain ⟨c, hc, hgc⟩ := real_root 2 3 (by norm_num) (by norm_num [cubic])
  have hab : a < b := by linarith [ha.2, hb.1]
  have hbc : b < c := by linarith [hb.2, hc.1]
  let e : Fin 3 → {φ : K →+* ℂ // ComplexEmbedding.IsReal φ} :=
    ![realEmbedding a hga, realEmbedding b hgb, realEmbedding c hgc]
  have hinj : Function.Injective e := by
    intro i j hij
    have h := congrArg (fun φ : {φ : K →+* ℂ // ComplexEmbedding.IsReal φ} =>
      (φ.val beta).re) hij
    fin_cases i <;> fin_cases j <;> simp [e, realEmbedding_beta] at h ⊢ <;> linarith
  have hreal : 3 ≤ nrRealPlaces K := by
    rw [← card_real_embeddings, ← Fintype.card_fin 3]
    exact Fintype.card_le_of_injective e hinj
  have hrank := card_add_two_mul_card_eq_rank K
  rw [finrank_K] at hrank
  omega

local notation "M" => (4 / π) ^ nrComplexPlaces K *
  ((Nat.factorial (Module.finrank ℚ K) : ℝ) / (Module.finrank ℚ K : ℝ) ^
    Module.finrank ℚ K * √|(NumberField.discr K : ℝ)|)

theorem minkowski_bound : M = (2 / 9 : ℝ) * √1556 := by
  rw [field_signature.2, finrank_K, field_discriminant]
  norm_num [Nat.factorial]

theorem minkowski_floor : ⌊M⌋₊ = 8 := by
  rw [minkowski_bound]
  have hlo : (36 : ℝ) ≤ √1556 := (Real.le_sqrt (by norm_num) (by norm_num)).2 (by norm_num)
  have hhi : √(1556 : ℝ) < 81 / 2 := (Real.sqrt_lt (by norm_num) (by norm_num)).2 (by norm_num)
  exact le_antisymm (Nat.lt_succ_iff.mp (Nat.floor_lt (by positivity) |>.2 (by norm_num; linarith)))
    (Nat.le_floor (by norm_num; linarith))

/-- The integral root in Mathlib's ring of integers. -/
def betaInteger : 𝓞 K :=
  ⟨beta, order_eq_integralClosure ▸ Algebra.self_mem_adjoin_singleton ℤ beta⟩

private theorem cubic_betaInteger : cubic betaInteger = 0 := by
  apply Subtype.ext
  change cubic beta = 0
  unfold cubic
  rw [beta_cubic]
  ring

theorem norm_betaInteger_sub (n : ℤ) :
    Algebra.norm ℤ (betaInteger - (n : 𝓞 K)) = FullDescent389.norm ⟨-n, 1, 0⟩ := by
  apply (Int.cast_injective (α := ℚ))
  rw [Algebra.coe_norm_int, ← norm_encode]
  congr 1
  change beta - (n : K) = encode ⟨-n, 1, 0⟩
  simp [encode]
  ring

theorem absNorm_betaInteger_sub_one : Ideal.absNorm (Ideal.span {betaInteger - 1}) = 2 := by
  rw [Ideal.absNorm_span_singleton, ← Int.cast_one, norm_betaInteger_sub]
  decide

theorem absNorm_betaInteger_sub_two : Ideal.absNorm (Ideal.span {betaInteger - 2}) = 3 := by
  rw [Ideal.absNorm_span_singleton, ← Int.cast_ofNat, norm_betaInteger_sub]
  decide

private theorem cubic_map {R S : Type*} [Ring R] [Ring S] (f : R →+* S) (x : R) :
    f (cubic x) = cubic (f x) := by simp [cubic, map_ofNat]

private theorem quotient_cubic (P : Ideal (𝓞 K)) : cubic (Ideal.Quotient.mk P betaInteger) = 0 := by
  rw [← cubic_map, cubic_betaInteger, map_zero]

private theorem prime_eq_span_of_mem {P : Ideal (𝓞 K)} (hP : P.IsPrime)
    {x : 𝓞 K} (hx : x ∈ P) (hN : (Ideal.absNorm (Ideal.span {x})).Prime) :
    P = Ideal.span {x} := by
  have hprime := Ideal.isPrime_of_irreducible_absNorm ((Nat.irreducible_iff_nat_prime _).mpr hN)
  have hne : Ideal.span {x} ≠ 0 := by
    intro h
    rw [h, map_zero] at hN
    exact Nat.not_prime_zero hN
  exact (hprime.isMaximal hne).eq_of_le hP.ne_top ((Ideal.span_singleton_le_iff_mem P).2 hx) |>.symm

theorem prime_over_two (P : Ideal (𝓞 K)) (hP : P.IsPrime) (h2 : (2 : 𝓞 K) ∈ P) :
    P = Ideal.span {betaInteger - 1} := by
  letI := hP
  have hz : (2 : (𝓞 K) ⧸ P) = 0 := by
    simpa only [map_ofNat] using (Ideal.Quotient.eq_zero_iff_mem).2 h2
  let x := Ideal.Quotient.mk P betaInteger
  have h := quotient_cubic P
  have hpow : (x - 1) ^ 3 = 0 := by
    calc
      (x - 1) ^ 3 = cubic x + 2 * (-x ^ 2 + 6 * x - 6) := by unfold cubic; ring
      _ = 0 := by rw [h, hz, zero_mul, zero_add]
  apply prime_eq_span_of_mem hP ?_ (by rw [absNorm_betaInteger_sub_one]; exact Nat.prime_two)
  apply (Ideal.Quotient.eq_zero_iff_mem).1
  rw [map_sub, map_one]
  exact pow_eq_zero hpow

private def primeQuotientEquiv (P : Ideal (𝓞 K)) {p : ℕ}
    (hp : p.Prime) (hN : Ideal.absNorm P = p) : ZMod p ≃+* ((𝓞 K) ⧸ P) := by
  have hc : Nat.card ((𝓞 K) ⧸ P) = p := by
    rwa [Ideal.absNorm_apply, Submodule.cardQuot_apply] at hN
  haveI : Finite ((𝓞 K) ⧸ P) := Nat.finite_of_card_ne_zero (hc.trans_ne hp.ne_zero)
  letI := Fintype.ofFinite ((𝓞 K) ⧸ P)
  exact ZMod.ringEquivOfPrime _ hp (by simpa only [Nat.card_eq_fintype_card] using hc)

private theorem cubic_mod_three (x : ZMod 3) (h : cubic x = 0) : x = 2 := by
  fin_cases x
  · exact False.elim ((by decide : cubic (0 : ZMod 3) ≠ 0) h)
  · exact False.elim ((by decide : cubic (1 : ZMod 3) ≠ 0) h)
  · rfl
private theorem cubic_mod_five (x : ZMod 5) : cubic x ≠ 0 := by fin_cases x <;> decide
private theorem cubic_mod_seven (x : ZMod 7) : cubic x ≠ 0 := by fin_cases x <;> decide

private theorem root_in_prime_quotient (P : Ideal (𝓞 K)) {p : ℕ}
    (hp : p.Prime) (hN : Ideal.absNorm P = p) :
    cubic ((primeQuotientEquiv P hp hN).symm (Ideal.Quotient.mk P betaInteger)) = 0 := by
  let f := (primeQuotientEquiv P hp hN).symm.toRingHom
  change cubic (f _) = 0
  rw [← cubic_map f, quotient_cubic, map_zero]

theorem prime_of_norm_three (P : Ideal (𝓞 K)) (hP : P.IsPrime) (hN : Ideal.absNorm P = 3) :
    P = Ideal.span {betaInteger - 2} := by
  apply prime_eq_span_of_mem hP ?_ (by rw [absNorm_betaInteger_sub_two]; exact Nat.prime_three)
  apply (Ideal.Quotient.eq_zero_iff_mem).1
  rw [map_sub, map_ofNat, sub_eq_zero]
  apply (primeQuotientEquiv P Nat.prime_three hN).symm.injective
  rw [map_ofNat]
  exact cubic_mod_three _ (root_in_prime_quotient P Nat.prime_three hN)

theorem no_ideal_of_norm_five (P : Ideal (𝓞 K)) : Ideal.absNorm P ≠ 5 :=
  fun hN => cubic_mod_five _ (root_in_prime_quotient P (by norm_num) hN)

theorem no_ideal_of_norm_seven (P : Ideal (𝓞 K)) : Ideal.absNorm P ≠ 7 :=
  fun hN => cubic_mod_seven _ (root_in_prime_quotient P (by norm_num) hN)

private theorem pow_eq_prime_of_small {p f : ℕ} (hp : 3 ≤ p) (hf : 0 < f)
    (h : p ^ f ≤ 8) : p ^ f = p := by
  have hf' : f = 1 := by
    by_contra hn
    have h₂ : 2 ≤ f := by omega
    have h₉ : 3 ^ 2 ≤ p ^ f :=
      (Nat.pow_le_pow_left hp 2).trans (Nat.pow_le_pow_right (by omega) h₂)
    omega
  simp [hf']

theorem integers_principal : IsPrincipalIdealRing (𝓞 K) := by
  apply RingOfIntegers.isPrincipalIdealRing_of_isPrincipal_of_pow_inertiaDeg_le_of_mem_primesOver_of_mem_Icc
  intro p hp hpprime P hP hbound
  rw [minkowski_floor] at hp hbound
  have hp8 := (Finset.mem_Icc.mp hp).2
  have hcases : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 := by
    interval_cases p <;> norm_num at hpprime ⊢
  rcases hP with ⟨hprime, hlies⟩
  letI := hlies
  have hip : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hpprime
  have hnorm := Ideal.absNorm_eq_pow_inertiaDeg P hip
  rw [Int.natAbs_natCast] at hnorm
  haveI : (Ideal.span {(p : ℤ)}).IsMaximal :=
    ((Ideal.span_singleton_prime hip.ne_zero).2 hip).isMaximal (by simp [hpprime.ne_zero])
  have hf := Ideal.inertiaDeg_pos (Ideal.span {(p : ℤ)}) P
  have hp_mem : (p : 𝓞 K) ∈ P := by
    change algebraMap ℤ (𝓞 K) (p : ℤ) ∈ P
    change (p : ℤ) ∈ P.under ℤ
    rw [← Ideal.over_def P (Ideal.span {(p : ℤ)})]
    exact Ideal.mem_span_singleton_self _
  rcases hcases with rfl | rfl | rfl | rfl
  · rw [prime_over_two P hprime hp_mem]
    exact ⟨_, rfl⟩
  · rw [prime_of_norm_three P hprime (hnorm.trans (pow_eq_prime_of_small (by decide) hf hbound))]
    exact ⟨_, rfl⟩
  · exact (no_ideal_of_norm_five P (hnorm.trans (pow_eq_prime_of_small (by decide) hf hbound))).elim
  · exact (no_ideal_of_norm_seven P (hnorm.trans (pow_eq_prime_of_small (by decide) hf hbound))).elim

/-- The cubic field associated with the 389a1 two-descent has class number one. -/
theorem class_number : NumberField.classNumber K = 1 :=
  NumberField.classNumber_eq_one_iff.mpr integers_principal

end CertifiedSelmer.Mathlib389.CubicField
