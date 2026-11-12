import Curve389
import CertifiedSelmer.FullDescent389
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import Mathlib.RingTheory.Adjoin.PowerBasis
import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime

/-! The rational division field and its power order for the 389a1 descent. -/

noncomputable section

namespace CertifiedSelmer.Mathlib389.CubicField
open Polynomial
open scoped Matrix
open CertifiedSelmer.FullDescent389 (CubicZ)

def gZ : ℤ[X] := X ^ 3 - X ^ 2 - C 9 * X + C 11

def g : ℚ[X] := gZ.map (algebraMap ℤ ℚ)

def shifted : ℤ[X] := X ^ 3 + C 2 * X ^ 2 - C 8 * X + C 2

theorem gZ_shift : gZ.comp (X + 1) = shifted := by
  simp [gZ, shifted, sub_comp, add_comp, mul_comp, pow_comp]
  ring

private lemma shifted_degree : shifted.natDegree = 3 := by
  unfold shifted
  compute_degree <;> norm_num

private lemma shifted_monic : shifted.Monic := by
  apply monic_of_natDegree_le_of_coeff_eq_one 3
  · rw [shifted_degree]
  · norm_num [shifted, Polynomial.coeff_X]

private lemma two_prime : Prime (2 : ℤ) := by
  exact Nat.prime_iff_prime_int.mp Nat.prime_two

private lemma two_ideal_prime : (Ideal.span ({(2 : ℤ)} : Set ℤ)).IsPrime :=
  (Ideal.span_singleton_prime (by norm_num)).2 two_prime

theorem shifted_eisenstein : shifted.IsEisensteinAt (Ideal.span ({(2 : ℤ)} : Set ℤ)) := by
  refine shifted_monic.isEisensteinAt_of_mem_of_notMem two_ideal_prime.ne_top ?_ ?_
  · intro n hn
    rw [shifted_degree] at hn
    rw [Ideal.mem_span_singleton]
    interval_cases n <;> norm_num [shifted, Polynomial.coeff_X]
  · rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    norm_num [shifted, Polynomial.coeff_X]

private lemma shifted_irreducible : Irreducible shifted :=
  shifted_eisenstein.irreducible two_ideal_prime shifted_monic.isPrimitive
    (by rw [shifted_degree]; decide)

private lemma gZ_degree : gZ.natDegree = 3 := by
  unfold gZ
  compute_degree <;> norm_num

private lemma gZ_monic : gZ.Monic := by
  apply monic_of_natDegree_le_of_coeff_eq_one 3
  · rw [gZ_degree]
  · norm_num [gZ, Polynomial.coeff_X]

theorem g_irreducible : Irreducible g := by
  apply (gZ_monic.irreducible_iff_irreducible_map_fraction_map (K := ℚ)).mp
  apply (MulEquiv.irreducible_iff (taylorEquiv (1 : ℤ)) (x := gZ)).mp
  change Irreducible (taylor 1 gZ)
  rw [taylor_apply, C_1, gZ_shift]
  exact shifted_irreducible

theorem divisionCubic_comp : divisionCubic.comp (C 2 * X - C 2) = C 8 * gZ := by
  simp [divisionCubic, gZ, sub_comp, add_comp, mul_comp, pow_comp]
  ring

abbrev K := AdjoinRoot g

instance : Fact (Irreducible g) := ⟨g_irreducible⟩

private lemma g_monic : g.Monic := gZ_monic.map _

def powerBasis : PowerBasis ℚ K := AdjoinRoot.powerBasis' g_monic

instance numberField : NumberField K where
  to_charZero := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  to_finiteDimensional := powerBasis.finite

theorem powerBasis_dim : powerBasis.dim = 3 := by
  change g.natDegree = 3
  rw [g, gZ_monic.natDegree_map, gZ_degree]

theorem finrank_K : Module.finrank ℚ K = 3 :=
  powerBasis.finrank.trans powerBasis_dim

def beta : K := AdjoinRoot.root g

def theta : K := 2 * beta - 2

private theorem gZ_beta : aeval beta gZ = 0 := by
  rw [← aeval_map_algebraMap ℚ]
  exact (AdjoinRoot.aeval_eq g).trans AdjoinRoot.mk_self

theorem beta_cubic : beta ^ 3 = beta ^ 2 + 9 * beta - 11 := by
  have h := gZ_beta
  simp only [gZ, map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C] at h
  change beta ^ 3 - beta ^ 2 - 9 * beta + 11 = 0 at h
  linear_combination h

theorem beta_quartic : beta ^ 4 = 10 * beta ^ 2 - 2 * beta - 11 := by
  linear_combination beta * beta_cubic + beta_cubic

theorem theta_root : aeval theta divisionCubic = 0 := by
  have h := congrArg (aeval beta : ℤ[X] →ₐ[ℤ] K) divisionCubic_comp
  rw [aeval_comp, map_mul, gZ_beta, mul_zero] at h
  have he : aeval beta (C 2 * X - C 2 : ℤ[X]) = theta := by
    simp only [map_sub, map_mul, aeval_C, aeval_X]
    rfl
  rwa [he] at h

/-- The basis of powers of β, indexed by Fin 3. -/
def basis : Basis (Fin 3) ℚ K :=
  powerBasis.basis.reindex (finCongr powerBasis_dim)

theorem basis_apply (i : Fin 3) : basis i = beta ^ i.val := by
  rw [basis, Basis.reindex_apply, powerBasis.basis_eq_pow]
  rfl

/-- Interpret an existing finite witness in the actual field. -/
def encode (x : CubicZ) : K := (x.a : K) + (x.b : K) * beta + (x.c : K) * beta ^ 2

theorem encode_mul (x y : CubicZ) : encode (FullDescent389.mul x y) = encode x * encode y := by
  simp only [encode, FullDescent389.mul, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_ofNat]
  linear_combination
    - ((x.b : K) * y.c + (x.c : K) * y.b) * beta_cubic -
    (x.c : K) * y.c * beta_quartic

theorem encode_scale (n : ℤ) (x : CubicZ) : encode (FullDescent389.scale n x) = (n : K) * encode x := by
  simp only [encode, FullDescent389.scale, Int.cast_mul]
  ring

theorem encode_one : encode FullDescent389.one = 1 := by simp [encode, FullDescent389.one]
theorem encode_zero : encode FullDescent389.zero = 0 := by simp [encode, FullDescent389.zero]

private theorem encode_eq_sum (x : CubicZ) :
    encode x = ∑ i, (![ (x.a : ℚ), (x.b : ℚ), (x.c : ℚ)] : Fin 3 → ℚ) i • basis i := by
  rw [Fin.sum_univ_three]
  simp [basis_apply, encode, Algebra.smul_def]

theorem repr_encode (x : CubicZ) (i : Fin 3) :
    basis.repr (encode x) i = (![ (x.a : ℚ), (x.b : ℚ), (x.c : ℚ)] : Fin 3 → ℚ) i := by
  rw [encode_eq_sum, Basis.repr_sum_self]

theorem encode_injective : Function.Injective encode := by
  intro x y h
  cases x with | mk a b c =>
    cases y with | mk a' b' c' =>
      have ha := congrArg (fun z => basis.repr z 0) h
      have hb := congrArg (fun z => basis.repr z 1) h
      have hc := congrArg (fun z => basis.repr z 2) h
      simp [repr_encode] at ha hb hc
      simp [ha, hb, hc]

private def mulMatrix (x : CubicZ) : Matrix (Fin 3) (Fin 3) ℚ :=
  let y := FullDescent389.mul x ⟨0, 1, 0⟩
  let z := FullDescent389.mul x ⟨0, 0, 1⟩
  !![x.a, y.a, z.a; x.b, y.b, z.b; x.c, y.c, z.c]

private theorem leftMulMatrix_encode (x : CubicZ) :
    Algebra.leftMulMatrix basis (encode x) = mulMatrix x := by
  ext i j
  rw [Algebra.leftMulMatrix_eq_repr_mul]
  have h₀ : basis 0 = 1 := by simp [basis_apply]
  have h₁ : basis 1 = encode ⟨0, 1, 0⟩ := by simp [basis_apply, encode]
  have h₂ : basis 2 = encode ⟨0, 0, 1⟩ := by simp [basis_apply, encode]
  fin_cases j <;> fin_cases i <;>
    simp [h₀, h₁, h₂, ← encode_mul, repr_encode, mulMatrix]

theorem norm_encode (x : CubicZ) : Algebra.norm ℚ (encode x) = (FullDescent389.norm x : ℚ) := by
  rw [Algebra.norm_eq_matrix_det basis, leftMulMatrix_encode, mulMatrix, Matrix.det_fin_three]
  simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.of_apply,
    Matrix.vecHead, Matrix.vecTail]
  dsimp
  push_cast [FullDescent389.norm, FullDescent389.det3]
  ring

theorem trace_encode (x : CubicZ) :
    Algebra.trace ℚ K (encode x) = 3 * (x.a : ℚ) + x.b + 19 * x.c := by
  rw [Algebra.trace_eq_matrix_trace basis, leftMulMatrix_encode, Matrix.trace, Fin.sum_univ_three]
  simp [mulMatrix, FullDescent389.mul]
  ring

theorem trace_matrix :
    Algebra.traceMatrix ℚ basis = !![3, 1, 19; 1, 19, -5; 19, -5, 155] := by
  have h (i : Fin 3) : basis i = encode (![FullDescent389.one, ⟨0, 1, 0⟩, ⟨0, 0, 1⟩] i) := by
    fin_cases i <;> simp [basis_apply, encode, FullDescent389.one]
  ext i j
  rw [Algebra.traceMatrix_apply, Algebra.traceForm_apply, h, h, ← encode_mul, trace_encode]
  fin_cases i <;> fin_cases j <;> norm_num [FullDescent389.mul, FullDescent389.one]

theorem powerBasis_discriminant : Algebra.discr ℚ basis = 1556 := by
  rw [Algebra.discr_def, trace_matrix, Matrix.det_fin_three]
  norm_num [Matrix.cons_val', Matrix.cons_val_two]

/-- Discriminant of the division-root powers, under θ = 2β − 2. -/
theorem division_power_discriminant :
    Algebra.discr ℚ (fun i : Fin 3 => theta ^ i.val) = 99584 := by
  let changeBasis : Matrix (Fin 3) (Fin 3) ℚ := !![1, 0, 0; -2, 2, 0; 4, -8, 4]
  have h : (fun i : Fin 3 => theta ^ i.val) =
      (changeBasis.map (algebraMap ℚ K)) *ᵥ (basis : Fin 3 → K) := by
    funext i
    fin_cases i <;>
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, changeBasis, basis_apply, theta] <;>
      ring
  rw [h, Algebra.discr_of_matrix_mulVec, powerBasis_discriminant]
  dsimp only [changeBasis]
  rw [Matrix.det_fin_three]
  norm_num [Matrix.cons_val', Matrix.cons_val_two]

theorem divisionCubic_eval_int (x : ℤ) :
    divisionCubic.eval x = FullDescent389.divisionCubic x := by
  simp [divisionCubic, FullDescent389.divisionCubic]
  ring

theorem norm_X_sub_theta (x : ℤ) :
    Algebra.norm ℚ ((x : K) - theta) = ((divisionCubic.eval x : ℤ) : ℚ) := by
  have h : (x : K) - theta = encode ⟨x + 2, -2, 0⟩ := by
    simp [encode, theta]
    ring
  rw [h, norm_encode, divisionCubic_eval_int]
  congr 1
  simp [FullDescent389.norm, FullDescent389.det3, FullDescent389.mul, FullDescent389.divisionCubic]
  ring

private abbrev F : ℚ[X] := divisionCubic.map (algebraMap ℤ ℚ)

theorem divisionCubic_irreducible : Irreducible F := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · rw [divisionCubic_monic.natDegree_map]
    have h : divisionCubic.natDegree = 3 := by
      unfold divisionCubic
      compute_degree <;> norm_num
    rw [h]
    decide
  · intro x hx
    apply divisionCubic_no_rat_root x
    rw [← aeval_map_algebraMap ℚ, coe_aeval_eq_eval]
    exact hx

private instance : Fact (Irreducible F) := ⟨divisionCubic_irreducible⟩

/-- The rational algebra defined by the division cubic is the same cubic field. -/
def divisionAlgebraEquiv : AdjoinRoot (divisionCubic.map (algebraMap ℤ ℚ)) ≃ₐ[ℚ] K := by
  let r := AdjoinRoot.root F
  have hr : aeval r divisionCubic = 0 := by
    rw [← aeval_map_algebraMap ℚ]
    exact (AdjoinRoot.aeval_eq F).trans AdjoinRoot.mk_self
  have hg : aeval ((r + 2) / 2) g = 0 := by
    change aeval ((r + 2) / 2) (gZ.map (algebraMap ℤ ℚ)) = 0
    rw [aeval_map_algebraMap]
    have h := congrArg (aeval ((r + 2) / 2) : ℤ[X] →ₐ[ℤ] AdjoinRoot F) divisionCubic_comp
    have harg : 2 * ((r + 2) / 2) - 2 = r := by ring
    have h' : (8 : AdjoinRoot F) * aeval ((r + 2) / 2) gZ = 0 := by
      rw [aeval_comp, map_mul] at h
      have heval : aeval ((r + 2) / 2) (C 2 * X - C 2 : ℤ[X]) = r := by
        simp only [map_sub, map_mul, aeval_C, aeval_X, map_ofNat]
        exact harg
      rw [heval, hr] at h
      rw [aeval_C] at h
      exact h.symm
    exact (mul_eq_zero.mp h').resolve_left (by norm_num)
  let f := AdjoinRoot.liftHom F theta (by exact (aeval_map_algebraMap ℚ _ _).trans theta_root)
  let inv := AdjoinRoot.liftHom g ((r + 2) / 2) hg
  refine AlgEquiv.ofAlgHom f inv ?_ ?_
  · apply AdjoinRoot.algHom_ext
    change f (inv beta) = beta
    have hf : f r = theta := by simp [f, r]
    have hi : inv beta = (r + 2) / 2 := by simp [inv, beta]
    simp only [hi, map_div₀, map_add, hf, map_ofNat, theta]
    ring
  · apply AdjoinRoot.algHom_ext
    change inv (f r) = r
    have hf : f r = theta := by simp [f, r]
    have hi : inv beta = (r + 2) / 2 := by simp [inv, beta]
    simp only [hf, theta, map_sub, map_mul, hi, map_ofNat]
    ring

theorem divisionAlgebraEquiv_root :
    divisionAlgebraEquiv (AdjoinRoot.root (divisionCubic.map (algebraMap ℤ ℚ))) = theta := by
  have h : aeval theta F = 0 := (aeval_map_algebraMap ℚ _ _).trans theta_root
  change AdjoinRoot.liftHom F theta h (AdjoinRoot.root F) = theta
  exact AdjoinRoot.liftHom_root F h

/-- The power order generated by the integral root β. -/
def order : Subalgebra ℤ K := Algebra.adjoin ℤ ({beta} : Set K)

theorem beta_integral : IsIntegral ℤ beta := ⟨gZ, gZ_monic, gZ_beta⟩

theorem encode_mem_order (x : CubicZ) : encode x ∈ order := by
  have hb : beta ∈ order := Algebra.self_mem_adjoin_singleton ℤ beta
  have hc (n : ℤ) : (n : K) ∈ order := by simpa using order.algebraMap_mem n
  exact order.add_mem (order.add_mem (hc x.a) (order.mul_mem (hc x.b) hb))
    (order.mul_mem (hc x.c) (order.pow_mem hb 2))

theorem mem_order_iff {z : K} : z ∈ order ↔ ∃ x : CubicZ, encode x = z := by
  let image : Subalgebra ℤ K :=
    { carrier := Set.range encode
      add_mem' := by
        rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
        refine ⟨⟨x.a + y.a, x.b + y.b, x.c + y.c⟩, ?_⟩
        simp only [encode, Int.cast_add]
        ring
      mul_mem' := by
        rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
        exact ⟨FullDescent389.mul x y, encode_mul x y⟩
      zero_mem' := ⟨FullDescent389.zero, encode_zero⟩
      one_mem' := ⟨FullDescent389.one, encode_one⟩
      algebraMap_mem' := fun n => ⟨⟨n, 0, 0⟩, by simp [encode]⟩ }
  constructor
  · intro hz
    have h : order ≤ image := Algebra.adjoin_le (by
      rw [Set.singleton_subset_iff]
      exact ⟨⟨0, 1, 0⟩, by simp [encode]⟩)
    exact h hz
  · rintro ⟨x, rfl⟩
    exact encode_mem_order x

theorem encode_integral (x : CubicZ) : IsIntegral ℤ (encode x) :=
  (adjoin_le_integralClosure beta_integral) (encode_mem_order x)

private theorem order_eq_shifted :
    order = Algebra.adjoin ℤ ({beta - 1} : Set K) := by
  apply le_antisymm <;> apply Algebra.adjoin_le <;> rw [Set.singleton_subset_iff]
  · have h := Algebra.self_mem_adjoin_singleton ℤ (beta - 1)
    simpa using (Algebra.adjoin ℤ {beta - 1}).add_mem h (Algebra.adjoin ℤ {beta - 1}).one_mem
  · exact order.sub_mem (Algebra.self_mem_adjoin_singleton ℤ beta) order.one_mem

private theorem shifted_root : aeval (beta - 1) shifted = 0 := by
  rw [← gZ_shift]
  rw [aeval_comp, map_add, aeval_X, map_one, sub_add_cancel, gZ_beta]

private theorem shifted_minpoly : minpoly ℤ (beta - 1) = shifted := by
  have hint : IsIntegral ℤ (beta - 1) := beta_integral.sub isIntegral_one
  apply Polynomial.map_injective (algebraMap ℤ ℚ) (IsFractionRing.injective ℤ ℚ)
  rw [← minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hint]
  symm
  apply minpoly.eq_of_irreducible_of_monic (A := ℚ) (x := beta - 1)
  · exact (shifted_monic.irreducible_iff_irreducible_map_fraction_map (K := ℚ)).mp
      shifted_irreducible
  · rw [aeval_map_algebraMap]
    exact shifted_root
  · exact shifted_monic.map _

private def shiftedPowerBasis : PowerBasis ℚ K :=
  powerBasis.ofGenMemAdjoin (IsIntegral.of_finite ℚ (beta - 1)) (by
    have h := Algebra.self_mem_adjoin_singleton ℚ (beta - 1)
    change beta ∈ Algebra.adjoin ℚ ({beta - 1} : Set K)
    simpa using (Algebra.adjoin ℚ {beta - 1}).add_mem h (Algebra.adjoin ℚ {beta - 1}).one_mem)

private theorem shiftedPowerBasis_gen : shiftedPowerBasis.gen = beta - 1 := by
  simp [shiftedPowerBasis]

/-- The order has no index contribution at 2, stated as saturation inside the integral closure. -/
theorem order_two_saturated {z : K} (hz : IsIntegral ℤ z) {n : ℕ}
    (h : (2 : ℤ) ^ n • z ∈ order) : z ∈ order := by
  rw [order_eq_shifted] at h ⊢
  apply mem_adjoin_of_smul_prime_pow_smul_of_minpoly_isEisensteinAt
    (B := shiftedPowerBasis) two_prime
    (show IsIntegral ℤ shiftedPowerBasis.gen by
      rw [shiftedPowerBasis_gen]
      exact beta_integral.sub isIntegral_one) hz
  · simpa [shiftedPowerBasis_gen] using h
  · simpa [shiftedPowerBasis_gen, shifted_minpoly] using shifted_eisenstein

/-- An existing finite cover witness, interpreted as an equation in the number field. -/
theorem lift_cover {δ : CubicZ} {X Y : ℤ} (h : FullDescent389.NormCoverWitness δ X Y) :
    Y ^ 2 = divisionCubic.eval X ∧
    ∃ z : K, encode δ * z ^ 2 = (X : K) - theta := by
  obtain ⟨hY, w, d, hd, hw⟩ := h
  refine ⟨by rwa [divisionCubic_eval_int], encode w / (d : K), ?_⟩
  have hw' := congrArg encode hw
  simp only [encode_mul, encode_scale, FullDescent389.sq, Int.cast_pow, Int.cast_natCast] at hw'
  have hd' : (d : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  rw [div_pow, ← mul_div_assoc, div_eq_iff (pow_ne_zero _ hd'), pow_two (encode w), hw']
  simp [encode, theta]
  ring

/-- The checked finite obstruction holds modulo 8 in the power order inside K. -/
theorem unitP_no_square_mod_eight {z w : K} (hz : z ∈ order) (hw : w ∈ order) :
    z ^ 2 - encode FullDescent389.unitP ≠ 8 * w := by
  intro he
  obtain ⟨x, rfl⟩ := mem_order_iff.mp hz
  obtain ⟨y, rfl⟩ := mem_order_iff.mp hw
  let u := FullDescent389.unitP
  let s := FullDescent389.sq x
  have hcoords : (⟨s.a - u.a, s.b - u.b, s.c - u.c⟩ : CubicZ) = FullDescent389.scale 8 y := by
    apply encode_injective
    rw [encode_scale]
    have hs : encode s = encode x ^ 2 := by simp [s, FullDescent389.sq, encode_mul, pow_two]
    have hd : encode ⟨s.a - u.a, s.b - u.b, s.c - u.c⟩ = encode s - encode u := by
      simp only [encode, Int.cast_sub]
      ring
    rw [hd, hs]
    exact he
  have ha := congrArg CubicZ.a hcoords
  have hb := congrArg CubicZ.b hcoords
  have hc := congrArg CubicZ.c hcoords
  change s.a - u.a = 8 * y.a at ha
  change s.b - u.b = 8 * y.b at hb
  change s.c - u.c = 8 * y.c at hc
  let residue (n : ℤ) : Fin 8 := ⟨(n % 8).toNat, by omega⟩
  have cast_residue (n : ℤ) : ((residue n).val : ZMod 8) = (n : ZMod 8) := by
    rw [← Int.cast_natCast, ZMod.intCast_eq_intCast_iff']
    change ((n % 8).toNat : ℤ) % 8 = n % 8
    omega
  let x' : CubicZ := ⟨(residue x.a).val, (residue x.b).val, (residue x.c).val⟩
  let s' := FullDescent389.sq x'
  have ha' : (s'.a : ZMod 8) = (s.a : ZMod 8) := by
    simp [s', s, x', FullDescent389.sq, FullDescent389.mul, cast_residue]
  have hb' : (s'.b : ZMod 8) = (s.b : ZMod 8) := by
    simp [s', s, x', FullDescent389.sq, FullDescent389.mul, cast_residue]
  have hc' : (s'.c : ZMod 8) = (s.c : ZMod 8) := by
    simp [s', s, x', FullDescent389.sq, FullDescent389.mul, cast_residue]
  rw [ZMod.intCast_eq_intCast_iff'] at ha' hb' hc'
  apply FullDescent389.unitP_not_square_mod_eight (residue x.a) (residue x.b) (residue x.c)
  change (s'.a - u.a) % 8 = 0 ∧ (s'.b - u.b) % 8 = 0 ∧ (s'.c - u.c) % 8 = 0
  exact ⟨by omega, by omega, by omega⟩

private theorem discr_powerBasis : Algebra.discr ℚ powerBasis.basis = 1556 := by
  rw [← Algebra.discr_reindex ℚ powerBasis.basis (finCongr powerBasis_dim)]
  simpa only [basis, Basis.coe_reindex] using powerBasis_discriminant

private theorem int_integral (n : ℤ) : IsIntegral ℤ (n : K) := by
  simpa using (isIntegral_algebraMap (R := ℤ) (A := K) (x := n))

/-- The discriminant clears denominators, and saturation at 2 removes its factor of 4. -/
theorem mul_389_mem_order {z : K} (hz : IsIntegral ℤ z) : 389 * z ∈ order := by
  have h := Algebra.discr_mul_isIntegral_mem_adjoin ℚ (R := ℤ) (B := powerBasis) beta_integral hz
  rw [discr_powerBasis, Algebra.smul_def] at h
  have h' : (2 : ℤ) ^ 2 • (389 * z) ∈ order := by
    convert h using 1
    simp only [Algebra.smul_def, map_pow, map_ofNat]
    ring
  exact order_two_saturated (by simpa using (int_integral 389).mul hz) h'

/-- Every algebraic integer is congruent modulo 8 to an element of the power order. -/
theorem integral_lift_mod_eight {z : K} (hz : IsIntegral ℤ z) :
    ∃ x : K, x ∈ order ∧ ∃ v : K, IsIntegral ℤ v ∧ z - x = 8 * v := by
  refine ⟨5 * (389 * z), order.mul_mem ?_ (mul_389_mem_order hz), -243 * z,
    by simpa using (int_integral (-243)).mul hz, by ring⟩
  simpa using order.algebraMap_mem (5 : ℤ)

/-- The modulo-eight obstruction holds in Mathlib's actual ring of integers. -/
theorem unitP_no_square_in_integers_mod_eight (z w : NumberField.RingOfIntegers K) :
    (z : K) ^ 2 - encode FullDescent389.unitP ≠ 8 * (w : K) := by
  intro he
  obtain ⟨x, hx, v, hv, h⟩ := integral_lift_mod_eight (show IsIntegral ℤ (z : K) from z.property)
  let q : K := (w : K) - v * ((z : K) + x)
  have hxint : IsIntegral ℤ x := (adjoin_le_integralClosure beta_integral) hx
  have hq : IsIntegral ℤ q := w.property.sub (hv.mul (z.property.add hxint))
  have heq : x ^ 2 - encode FullDescent389.unitP = 8 * q := by
    unfold q
    linear_combination he - ((z : K) + x) * h
  have hqmem : q ∈ order := by
    apply order_two_saturated (n := 3) hq
    have h8 : (2 : ℤ) ^ 3 • q = 8 * q := by norm_num [Algebra.smul_def]
    rw [h8, ← heq]
    exact order.sub_mem (order.pow_mem hx 2) (encode_mem_order _)
  exact unitP_no_square_mod_eight hx hqmem heq

/-- The finite obstruction also rules out a square root of the unit in K itself. -/
theorem unitP_not_isSquare : ¬ IsSquare (encode FullDescent389.unitP) := by
  rintro ⟨z, hz⟩
  have hs : z ^ 2 = encode FullDescent389.unitP := by simpa [pow_two] using hz.symm
  have hint : IsIntegral ℤ z :=
    IsIntegral.of_pow (by decide : 0 < 2) (hs.symm ▸ encode_integral _)
  have h := unitP_no_square_in_integers_mod_eight ⟨z, hint⟩ 0
  apply h
  change z ^ 2 - encode FullDescent389.unitP = 8 * (0 : K)
  rw [hs, sub_self, mul_zero]

private theorem order_and_discriminant :
    order = integralClosure ℤ K ∧ NumberField.discr K = 1556 := by
  classical
  let b := NumberField.integralBasis K
  let e := basis.reindex (basis.indexEquiv b)
  have he (i) : e i ∈ order := by
    rw [show e i = basis ((basis.indexEquiv b).symm i) from Basis.reindex_apply _ _ _,
      basis_apply]
    exact order.pow_mem (Algebra.self_mem_adjoin_singleton ℤ beta) _
  let A := b.toMatrix e
  let B := e.toMatrix b
  -- The columns of A are the power basis in integral-basis coordinates.
  have hA : ∀ i j, IsIntegral ℤ (A i j) := by
    intro i j
    let z : NumberField.RingOfIntegers K := ⟨e j, (adjoin_le_integralClosure beta_integral) (he j)⟩
    change IsIntegral ℤ (b.repr (algebraMap _ _ z) i)
    rw [NumberField.integralBasis_repr_apply]
    exact isIntegral_algebraMap
  -- The existing denominator bound makes the scaled inverse integral.
  have hB : ∀ i j, IsIntegral ℤ (((389 : ℚ) • B) i j) := by
    intro i j
    have hb : IsIntegral ℤ (b j) := by
      rw [NumberField.integralBasis_apply]
      exact (NumberField.RingOfIntegers.basis K j).property
    obtain ⟨x, hx⟩ := mem_order_iff.mp (mul_389_mem_order hb)
    change IsIntegral ℤ ((389 : ℚ) • e.repr (b j) i)
    rw [← Finsupp.smul_apply, ← map_smul]
    have hscale : (389 : ℚ) • b j = 389 * b j := by norm_num [Algebra.smul_def]
    rw [hscale, ← hx]
    simp only [e, Basis.repr_reindex_apply, repr_encode]
    generalize (basis.indexEquiv b).symm i = k
    fin_cases k <;> exact isIntegral_algebraMap
  obtain ⟨d, hd⟩ := IsIntegrallyClosed.isIntegral_iff.mp (IsIntegral.det hA)
  obtain ⟨f, hf⟩ := IsIntegrallyClosed.isIntegral_iff.mp (IsIntegral.det hB)
  change (d : ℚ) = A.det at hd
  change (f : ℚ) = ((389 : ℚ) • B).det at hf
  have hdisc : 1556 = d ^ 2 * NumberField.discr K := by
    apply (Int.cast_injective (α := ℚ))
    push_cast
    rw [NumberField.coe_discr, hd]
    change (1556 : ℚ) = (b.toMatrix e).det ^ 2 * Algebra.discr ℚ b
    calc
      (1556 : ℚ) = Algebra.discr ℚ e := by
        simpa only [e, Basis.coe_reindex, Algebra.discr_reindex] using powerBasis_discriminant.symm
      _ = (b.toMatrix e).det ^ 2 * Algebra.discr ℚ b := by
        have h := b.toMatrix_map_vecMul e
        rw [← Algebra.discr_of_matrix_vecMul, h]
  have hprod : d * f = 389 ^ 3 := by
    apply (Int.cast_injective (α := ℚ))
    push_cast only [Int.cast_mul, Int.cast_pow, Int.cast_ofNat]
    rw [hd, hf, Matrix.det_smul, ← mul_assoc, mul_comm A.det, mul_assoc, ← Matrix.det_mul]
    have hab : A * B = 1 := Basis.toMatrix_mul_toMatrix_flip b e
    rw [hab, Matrix.det_one, mul_one]
    congr 1
    rw [Fintype.card_congr (basis.indexEquiv b).symm, Fintype.card_fin]
  have hd₁ : d ∣ (389 : ℤ) ^ 3 := ⟨f, hprod.symm⟩
  have hd₂ : d ^ 2 ∣ (1556 : ℤ) := ⟨_, hdisc⟩
  have hd₃ : d ∣ (389 : ℤ) := by
    have h1556 : d ∣ (1556 : ℤ) := dvd_trans (dvd_pow_self _ (by decide)) hd₂
    -- The gcd of the two multiples of d is 389.
    have h := dvd_sub hd₁ (dvd_mul_of_dvd_right h1556 (37830 : ℤ))
    norm_num at h
    exact h
  have hp : Prime (389 : ℤ) := Nat.prime_iff_prime_int.mp (by norm_num)
  have hu : IsUnit d := by
    rcases hp.irreducible.dvd_iff.mp hd₃ with h | h
    · exact h
    · have hdvd : (389 : ℤ) ∣ d := h.dvd
      have hs : (389 : ℤ) ^ 2 ∣ (1556 : ℤ) := dvd_trans (pow_dvd_pow_of_dvd hdvd _) hd₂
      norm_num at hs
  have hdiscK : NumberField.discr K = 1556 := by
    rcases Int.isUnit_iff.mp hu with h | h <;> simp [h] at hdisc <;> exact hdisc.symm
  refine ⟨?_, hdiscK⟩
  -- A unit determinant over ℤ gives an integer inverse.
  have hBintegral : ∀ i j, IsIntegral ℤ (B i j) := by
    choose entries hentries using fun i j => IsIntegrallyClosed.isIntegral_iff.mp (hA i j)
    let C : Matrix _ _ ℤ := entries
    have hC : C.map (Int.castRingHom ℚ) = A := by
      ext i j
      exact hentries i j
    have hCd : C.det = d := by
      apply (Int.cast_injective (α := ℚ))
      change Int.castRingHom ℚ C.det = Int.castRingHom ℚ d
      rw [RingHom.map_det]
      change (C.map (Int.castRingHom ℚ)).det = (d : ℚ)
      rw [hC]
      exact hd.symm
    obtain ⟨u, huC⟩ := (Matrix.isUnit_iff_isUnit_det C).mpr (hCd.symm ▸ hu)
    let φ := (Int.castRingHom ℚ).mapMatrix
      (m := Module.Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers K))
    have hCinv : A * φ (↑u⁻¹) = 1 := by
      rw [← map_one φ]
      rw [← hC, ← show φ C = C.map (Int.castRingHom ℚ) from rfl,
        ← map_mul, ← huC, Units.mul_inv]
    have hBA : B * A = 1 := Basis.toMatrix_mul_toMatrix_flip e b
    have h : B = φ (↑u⁻¹) := by
      rw [← mul_one B, ← hCinv, ← mul_assoc, hBA, one_mul]
    intro i j
    rw [h]
    exact isIntegral_algebraMap
  apply le_antisymm (adjoin_le_integralClosure beta_integral)
  intro z hz
  let z' : NumberField.RingOfIntegers K := ⟨z, hz⟩
  have hre (i) : IsIntegral ℤ (e.repr z i) := by
    rw [← Basis.toMatrix_mulVec_repr b e z]
    change IsIntegral ℤ (∑ j, B i j * b.repr z j)
    apply IsIntegral.sum
    intro j _
    have hzj : IsIntegral ℤ (b.repr z j) := by
      change IsIntegral ℤ (b.repr (algebraMap _ _ z') j)
      rw [NumberField.integralBasis_repr_apply]
      exact isIntegral_algebraMap
    exact (hBintegral i j).mul hzj
  rw [← e.sum_repr z]
  apply order.sum_mem
  intro i _
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp (hre i)
  rw [← hn, Algebra.smul_def, ← IsScalarTower.algebraMap_apply]
  exact order.mul_mem (order.algebraMap_mem n) (he i)

/-- The power order is the full integral closure of ℤ in the cubic field. -/
theorem order_eq_integralClosure : order = integralClosure ℤ K :=
  order_and_discriminant.1

/-- The discriminant of the cubic number field for the 389a1 descent. -/
theorem field_discriminant : NumberField.discr K = 1556 :=
  order_and_discriminant.2

end CertifiedSelmer.Mathlib389.CubicField
