import ClassNumber389
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.Algebra.Module.ZMod
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Integral-unit squareclasses of the cubic division field of 389a1. -/

noncomputable section

namespace CertifiedSelmer.Mathlib389.CubicField

open NumberField
open scoped BigOperators
open scoped NumberField
open NumberField.InfinitePlace

local notation "U" => (𝓞 K)ˣ
local notation "T" => NumberField.Units.torsion K
local notation "M₂" => Multiplicative (Fin 2 → ZMod 2)

local instance : Module ℤ (Additive (U ⧸ T)) := AddCommGroup.toIntModule (Additive (U ⧸ T))

theorem unit_rank : NumberField.Units.rank K = 2 := by
  rw [NumberField.Units.rank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    field_signature.1, field_signature.2]

theorem unit_rank_mod_torsion : Module.finrank ℤ (Additive (U ⧸ T)) = 2 :=
  (NumberField.Units.rank_modTorsion K).trans unit_rank

private def unitBasis : Basis (Fin 2) ℤ (Additive (U ⧸ T)) :=
  unit_rank ▸ NumberField.Units.basisModTorsion K

/-- The integral norm, restricted to units. -/
def unitNorm : U →* ℤˣ := Units.map (Algebra.norm ℤ : 𝓞 K →* ℤ)

theorem coe_unitNorm (u : U) : ((unitNorm u : ℤ) : ℚ) = Algebra.norm ℚ (u : K) :=
  Algebra.coe_norm_int (u : 𝓞 K)

@[simp] theorem unitNorm_neg_one : unitNorm (-1) = -1 := by
  apply Units.ext
  apply (Int.cast_injective (α := ℚ))
  rw [coe_unitNorm, NumberField.Units.coe_neg_one]
  have h : (-1 : K) = algebraMap ℚ K (-1) := by simp
  rw [h, Algebra.norm_algebraMap, finrank_K]
  norm_num

private theorem torsion_sign {u : U} (hu : u ∈ T) : u = 1 ∨ u = -1 := by
  obtain ⟨e, _, _⟩ := exists_real_embedding_beta_between_two_three
  let φ := Complex.ofRealHom.comp e
  let w : InfinitePlace K := InfinitePlace.mk φ
  have h := (NumberField.Units.mem_torsion K).mp hu w
  change ‖((e (u : K) : ℝ) : ℂ)‖ = 1 at h
  rw [Complex.norm_real, Real.norm_eq_abs] at h
  rcases abs_eq_abs.mp (h.trans (abs_one : |(1 : ℝ)| = 1).symm) with h | h
  · left
    apply NumberField.Units.coe_injective K
    exact e.injective (by simpa [NumberField.Units.coe_one] using h)
  · right
    apply NumberField.Units.coe_injective K
    exact e.injective (by simpa [NumberField.Units.coe_neg_one] using h)

private def coordinates : U →* Multiplicative (Fin 2 → ℤ) where
  toFun u := Multiplicative.ofAdd (unitBasis.equivFun (Additive.ofMul (QuotientGroup.mk u)))
  map_one' := by change unitBasis.equivFun 0 = 0; simp
  map_mul' u v := by
    change unitBasis.equivFun (Additive.ofMul (QuotientGroup.mk (u * v))) =
      unitBasis.equivFun (Additive.ofMul (QuotientGroup.mk u)) +
        unitBasis.equivFun (Additive.ofMul (QuotientGroup.mk v))
    rw [QuotientGroup.mk_mul]
    exact unitBasis.equivFun.map_add (Additive.ofMul (QuotientGroup.mk u))
      (Additive.ofMul (QuotientGroup.mk v))

private theorem coordinates_surjective : Function.Surjective coordinates := by
  intro x
  obtain ⟨q, hq⟩ := QuotientGroup.mk'_surjective T
    ((unitBasis.equivFun.symm x.toAdd).toMul)
  refine ⟨q, ?_⟩
  change unitBasis.equivFun (Additive.ofMul (QuotientGroup.mk' T q)) = x.toAdd
  rw [hq]
  exact unitBasis.equivFun.apply_symm_apply _

private theorem coordinates_eq_one {u : U} : coordinates u = 1 ↔ u ∈ T := by
  change unitBasis.equivFun (Additive.ofMul (QuotientGroup.mk u)) = 0 ↔ _
  rw [LinearEquiv.map_eq_zero_iff]
  exact QuotientGroup.eq_one_iff u

private def parity : Multiplicative (Fin 2 → ℤ) →* M₂ where
  toFun x := Multiplicative.ofAdd (fun i => (x.toAdd i : ZMod 2))
  map_one' := by rfl
  map_mul' x y := by
    change (fun i => ((x.toAdd i + y.toAdd i : ℤ) : ZMod 2)) = _
    funext i
    exact Int.cast_add _ _

private theorem parity_sq (x : M₂) : x ^ 2 = 1 := by
  change (fun i => 2 • x.toAdd i) = 0
  ext i
  rw [two_nsmul, ← two_mul]
  exact (show (2 : ZMod 2) = 0 by decide) ▸ zero_mul _

private def signedParity : U →* ℤˣ × M₂ :=
  unitNorm.prod (parity.comp coordinates)

private theorem signedParity_surjective : Function.Surjective signedParity := by
  rintro ⟨s, x⟩
  choose z hz using fun i => ZMod.intCast_surjective (x.toAdd i)
  obtain ⟨u, hu⟩ := coordinates_surjective (Multiplicative.ofAdd z)
  have hpar : parity (coordinates u) = x := by rw [hu]; exact funext hz
  have hneg : coordinates (-1) = 1 := by
    apply coordinates_eq_one.mpr
    change (-1 : U) ∈ CommGroup.torsion U
    rw [CommGroup.mem_torsion]
    exact isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by decide, neg_one_sq⟩
  rcases Int.units_eq_one_or (unitNorm u) with h | h <;>
    rcases Int.units_eq_one_or s with rfl | rfl
  · exact ⟨u, Prod.ext h hpar⟩
  · refine ⟨(-1) * u, Prod.ext ?_ ?_⟩
    · change unitNorm ((-1) * u) = -1
      rw [map_mul, unitNorm_neg_one, h, mul_one]
    · change parity (coordinates ((-1) * u)) = x
      rw [map_mul, hneg, one_mul, hpar]
  · refine ⟨(-1) * u, Prod.ext ?_ ?_⟩
    · change unitNorm ((-1) * u) = 1
      rw [map_mul, unitNorm_neg_one, h, neg_one_mul, neg_neg]
    · change parity (coordinates ((-1) * u)) = x
      rw [map_mul, hneg, one_mul, hpar]
  · exact ⟨u, Prod.ext h hpar⟩

/-- The subgroup of squares of integral units. -/
def unitSquares : Subgroup U := (powMonoidHom 2 : U →* U).range

private theorem unitNorm_sq (u : U) : unitNorm (u ^ 2) = 1 := by
  rw [map_pow]
  rcases Int.units_eq_one_or (unitNorm u) with h | h <;> simp [h]

private theorem signedParity_ker : signedParity.ker = unitSquares := by
  ext u
  constructor
  · intro h
    have hn : unitNorm u = 1 := congrArg Prod.fst h
    have hp : parity (coordinates u) = 1 := congrArg Prod.snd h
    have he (i : Fin 2) : (2 : ℤ) ∣ (coordinates u).toAdd i := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp
      exact congrArg (fun v : M₂ => v.toAdd i) hp
    choose z hz using he
    obtain ⟨v, hv⟩ := coordinates_surjective (Multiplicative.ofAdd z)
    have hc : coordinates (v ^ 2) = coordinates u := by
      rw [map_pow, hv]
      change (fun i => 2 • z i) = (coordinates u).toAdd
      funext i
      rw [hz i]
      simp [two_nsmul, two_mul]
    have ht : u / v ^ 2 ∈ T := by
      apply coordinates_eq_one.mp
      rw [map_div, hc, div_self']
    have hnt : unitNorm (u / v ^ 2) = 1 := by rw [map_div, hn, unitNorm_sq, div_one]
    rcases torsion_sign ht with h1 | h1
    · exact ⟨v, (div_eq_one.mp h1).symm⟩
    · rw [h1, unitNorm_neg_one] at hnt
      exact ((by decide : (-1 : ℤˣ) ≠ 1) hnt).elim
  · rintro ⟨v, rfl⟩
    apply MonoidHom.mem_ker.mpr
    apply Prod.ext
    · exact unitNorm_sq v
    · exact (parity.comp coordinates).map_pow v 2 |>.trans (parity_sq _)

/-- The unit squareclass group, in norm-sign and Dirichlet parity coordinates. -/
def unitSquareclassEquiv : U ⧸ unitSquares ≃* ℤˣ × M₂ := by
  refine (QuotientGroup.quotientMulEquivOfEq signedParity_ker.symm).trans ?_
  exact QuotientGroup.quotientKerEquivOfSurjective signedParity signedParity_surjective

/-- The norm on unit squareclasses. Its target already has exponent two. -/
def squareclassNorm : U ⧸ unitSquares →* ℤˣ :=
  QuotientGroup.lift unitSquares unitNorm (by rintro _ ⟨v, rfl⟩; exact unitNorm_sq v)

@[simp] theorem squareclassNorm_mk (u : U) : squareclassNorm (QuotientGroup.mk u) = unitNorm u :=
  rfl

theorem squareclassNorm_eq_fst (x : U ⧸ unitSquares) :
    squareclassNorm x = (unitSquareclassEquiv x).1 := by
  refine Quotient.inductionOn' x ?_
  intro u
  simp only [unitSquareclassEquiv, MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

/-- The norm-square kernel has two independent parity coordinates. -/
def normSquareKernelEquiv : squareclassNorm.ker ≃* M₂ where
  toFun x := (unitSquareclassEquiv x.val).2
  invFun y := ⟨unitSquareclassEquiv.symm (1, y), by
    rw [MonoidHom.mem_ker, squareclassNorm_eq_fst, MulEquiv.apply_symm_apply]⟩
  left_inv x := by
    apply Subtype.ext
    apply unitSquareclassEquiv.injective
    rw [MulEquiv.apply_symm_apply]
    exact Prod.ext ((squareclassNorm_eq_fst x.val).symm.trans x.property).symm rfl
  right_inv y := by simp
  map_mul' x y := by change (unitSquareclassEquiv (x.val * y.val)).2 = _; rw [map_mul]; rfl

instance : Module (ZMod 2) (Additive squareclassNorm.ker) :=
  AddCommGroup.zmodModule (n := 2) (G := Additive squareclassNorm.ker) (fun x => by
    apply normSquareKernelEquiv.injective
    change normSquareKernelEquiv (x.toMul ^ 2) = normSquareKernelEquiv 1
    rw [map_pow, map_one, parity_sq])

private def normSquareKernelLinearEquiv :
    Additive squareclassNorm.ker ≃ₗ[ZMod 2] (Fin 2 → ZMod 2) :=
  LinearEquiv.ofBijective (normSquareKernelEquiv.toAdditive'.toAddMonoidHom.toZModLinearMap 2)
    normSquareKernelEquiv.toAdditive'.bijective

theorem norm_square_kernel_finrank :
    Module.finrank (ZMod 2) (Additive squareclassNorm.ker) = 2 := by
  rw [normSquareKernelLinearEquiv.finrank_eq, Module.finrank_pi]
  simp

theorem norm_square_kernel_card : Nat.card squareclassNorm.ker = 4 := by
  rw [Nat.card_congr normSquareKernelEquiv.toEquiv]
  change Nat.card (Fin 2 → ZMod 2) = 4
  rw [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  decide

/-- The rational norm of a unit is a square precisely when its integral norm is +1. -/
theorem unitNorm_isSquare_iff (u : U) : IsSquare (Algebra.norm ℚ (u : K)) ↔ unitNorm u = 1 := by
  rw [← coe_unitNorm]
  rcases Int.units_eq_one_or (unitNorm u) with h | h
  · rw [h]
    exact iff_of_true (by exact ⟨1, by norm_num⟩) rfl
  · rw [h]
    refine iff_of_false ?_ (by decide)
    rintro ⟨r, hr⟩
    norm_num at hr
    nlinarith [sq_nonneg r]

open FullDescent389 (CubicZ)

private def integralEncode (x : CubicZ) : 𝓞 K := ⟨encode x, encode_integral x⟩

private theorem integralEncode_isUnit (x : CubicZ) (h : FullDescent389.norm x = 1) :
    IsUnit (integralEncode x) := by
  apply NumberField.isUnit_iff_norm.mpr
  rw [RingOfIntegers.coe_norm]
  change |Algebra.norm ℚ (encode x)| = 1
  rw [norm_encode, h]
  norm_num

private def unitOfNormOne (x : CubicZ) (h : FullDescent389.norm x = 1) : U :=
  (integralEncode_isUnit x h).unit

/-- Integral representatives obtained from the checked finite descent witnesses. -/
def descentUnitP : U := unitOfNormOne FullDescent389.unitP FullDescent389.norm_unitP

def descentUnitQ : U := unitOfNormOne FullDescent389.unitQ FullDescent389.norm_unitQ

private theorem coe_unitOfNormOne (x : CubicZ) (h : FullDescent389.norm x = 1) :
    (unitOfNormOne x h : K) = encode x :=
  congrArg (fun y : 𝓞 K => (y : K)) (IsUnit.unit_spec (integralEncode_isUnit x h))

@[simp] theorem coe_descentUnitP : (descentUnitP : K) = encode FullDescent389.unitP :=
  coe_unitOfNormOne _ _

@[simp] theorem coe_descentUnitQ : (descentUnitQ : K) = encode FullDescent389.unitQ :=
  coe_unitOfNormOne _ _

@[simp] theorem norm_descentUnitP : unitNorm descentUnitP = 1 := by
  apply Units.ext
  apply (Int.cast_injective (α := ℚ))
  rw [coe_unitNorm, coe_descentUnitP, norm_encode, FullDescent389.norm_unitP]
  rfl

@[simp] theorem norm_descentUnitQ : unitNorm descentUnitQ = 1 := by
  apply Units.ext
  apply (Int.cast_injective (α := ℚ))
  rw [coe_unitNorm, coe_descentUnitQ, norm_encode, FullDescent389.norm_unitQ]
  rfl

theorem descentUnitP_normalizes :
    (beta - 3) ^ 4 * (descentUnitP : K) = encode FullDescent389.alphaP := by
  rw [coe_descentUnitP, ← FullDescent389.normalize_P]
  simp only [encode_mul, FullDescent389.sq]
  have hp : encode FullDescent389.pi = beta - 3 := by
    norm_num [encode, FullDescent389.pi]
    ring
  rw [hp]
  ring

theorem descentUnitQ_normalizes :
    (beta - 3) ^ 4 * (descentUnitQ : K) = encode FullDescent389.alphaQ := by
  rw [coe_descentUnitQ, ← FullDescent389.normalize_Q]
  simp only [encode_mul, FullDescent389.sq]
  have hp : encode FullDescent389.pi = beta - 3 := by
    norm_num [encode, FullDescent389.pi]
    ring
  rw [hp]
  ring

theorem descentUnitP_nonsquare : ¬ IsSquare (descentUnitP : K) := by
  rw [coe_descentUnitP]
  exact unitP_not_isSquare

open scoped nonZeroDivisors

/-- The principal fractional ideal criterion underlying the even-valuation descent step. -/
theorem exists_unit_of_square_fractional_ideal {a : K} (ha : a ≠ 0)
    (I : FractionalIdeal (𝓞 K)⁰ K)
    (hI : FractionalIdeal.spanSingleton (𝓞 K)⁰ a = I ^ 2) :
    ∃ (u : U) (b : K), b ≠ 0 ∧ a = (u : K) * b ^ 2 := by
  letI := integers_principal
  obtain ⟨b, hb⟩ := (FractionalIdeal.isPrincipal_iff I).mp inferInstance
  rw [hb, pow_two, FractionalIdeal.spanSingleton_mul_spanSingleton] at hI
  obtain ⟨u, hu⟩ := FractionalIdeal.spanSingleton_eq_spanSingleton.mp hI.symm
  change (u : K) * (b * b) = a at hu
  refine ⟨u, b, ?_, by simpa [pow_two] using hu.symm⟩
  intro hz
  subst b
  exact ha (by simpa using hu.symm)

private theorem integralEncode_polynomial (x : CubicZ) :
    integralEncode x = (x.a : 𝓞 K) + (x.b : 𝓞 K) * betaInteger +
      (x.c : 𝓞 K) * betaInteger ^ 2 := by
  apply Subtype.ext
  rfl

theorem descentUnitQ_nonsquare : ¬ IsSquare (descentUnitQ : K) := by
  rintro ⟨z, hz⟩
  have hz' : z ^ 2 = encode FullDescent389.unitQ := by
    simpa [pow_two] using hz.symm
  let zi : 𝓞 K := ⟨z, IsIntegral.of_pow (by decide : 0 < 2)
    (hz'.symm ▸ encode_integral _)⟩
  have hs : zi ^ 2 = integralEncode FullDescent389.unitQ := Subtype.ext hz'
  let P : Ideal (𝓞 K) := Ideal.span {betaInteger - 2}
  let f : 𝓞 K →+* ZMod 3 :=
    (primeQuotientEquiv P Nat.prime_three absNorm_betaInteger_sub_two).symm.toRingHom.comp
      (Ideal.Quotient.mk P)
  have hf : f betaInteger = 2 := by
    have hm : betaInteger - 2 ∈ P := Ideal.subset_span (Set.mem_singleton _)
    have h := congrArg (primeQuotientEquiv P Nat.prime_three
      absNorm_betaInteger_sub_two).symm ((Ideal.Quotient.eq_zero_iff_mem).mpr hm)
    change f (betaInteger - 2) = f 0 at h
    simpa only [map_sub, map_zero, map_ofNat, sub_eq_zero] using h
  have h := congrArg f hs
  rw [map_pow, integralEncode_polynomial, map_add, map_add, map_mul, map_mul,
    map_pow, hf, map_intCast, map_intCast, map_intCast] at h
  have hval : f zi ^ 2 = (2 : ZMod 3) := h.trans (by decide)
  exact (show ∀ x : ZMod 3, x ^ 2 ≠ 2 by decide) _ hval

theorem descentUnitProduct_nonsquare :
    ¬ IsSquare ((descentUnitP : K) * (descentUnitQ : K)) := by
  obtain ⟨e, he2, he3⟩ := exists_real_embedding_beta_between_two_three
  have hP := congrArg e descentUnitP_normalizes
  have hQ := congrArg e descentUnitQ_normalizes
  simp only [map_mul, map_pow, map_sub, map_ofNat] at hP hQ
  rw [show encode FullDescent389.alphaP = 2 - 2 * beta by
    norm_num [encode, FullDescent389.alphaP]; ring] at hP
  rw [show encode FullDescent389.alphaQ = 6 - 2 * beta by
    norm_num [encode, FullDescent389.alphaQ]; ring] at hQ
  simp only [map_sub, map_mul, map_ofNat] at hP hQ
  have hpow : 0 < (e beta - 3) ^ 4 := by
    rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul]
    exact pow_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr he3.ne)) _
  have hp : e (descentUnitP : K) < 0 := by
    have h : (e beta - 3) ^ 4 * e (descentUnitP : K) < 0 := by rw [hP]; linarith
    by_contra! hnonneg
    exact (not_lt_of_ge (mul_nonneg hpow.le hnonneg)) h
  have hq : 0 < e (descentUnitQ : K) := by
    have h : 0 < (e beta - 3) ^ 4 * e (descentUnitQ : K) := by rw [hQ]; linarith
    exact (mul_pos_iff_of_pos_left hpow).mp h
  rintro ⟨x, hx⟩
  have h := congrArg e hx
  simp only [map_mul] at h
  linarith [mul_neg_of_neg_of_pos hp hq, mul_self_nonneg (e x)]

/-- A nonzero element with even valuations at every finite prime is a unit times a square. -/
theorem exists_unit_of_even_valuations {a : K} (ha : a ≠ 0)
    (he : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      Even (FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ a))) :
    ∃ (u : U) (b : K), b ≠ 0 ∧ a = (u : K) * b ^ 2 := by
  classical
  let A := FractionalIdeal.spanSingleton (𝓞 K)⁰ a
  have hA : A ≠ 0 := FractionalIdeal.spanSingleton_ne_zero_iff.mpr ha
  let half (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :=
    (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ (FractionalIdeal.count K v A / 2)
  have hfinite : (Function.mulSupport half).Finite := by
    have hf := FractionalIdeal.finite_factors A
    rw [Filter.eventually_cofinite] at hf
    apply hf.subset
    intro v hv hzero
    apply hv
    simp [half, hzero]
  apply exists_unit_of_square_fractional_ideal ha (∏ᶠ v, half v)
  rw [finprod_pow hfinite]
  calc
    A = ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
        (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ FractionalIdeal.count K v A :=
      (FractionalIdeal.finprod_heightOneSpectrum_factorization' K hA).symm
    _ = ∏ᶠ v, half v ^ 2 := by
      congr 1
      funext v
      dsimp [half]
      rw [← zpow_natCast, ← zpow_mul]
      congr 1
      obtain ⟨n, hn⟩ := he v
      change FractionalIdeal.count K v A = n + n at hn
      omega

private theorem field_nonsquare_class_ne_one (u : U) (h : ¬ IsSquare (u : K)) :
    (QuotientGroup.mk u : U ⧸ unitSquares) ≠ 1 := by
  intro he
  obtain ⟨v, hv⟩ := (QuotientGroup.eq_one_iff u).mp he
  apply h
  refine ⟨(v : K), ?_⟩
  have hv' := congrArg (fun w : U => (w : K)) hv
  simpa [powMonoidHom, NumberField.Units.coe_pow, pow_two] using hv'.symm

/-- The classes of P and Q and their product in the norm-square kernel. -/
def classP : squareclassNorm.ker := ⟨QuotientGroup.mk descentUnitP, by simp⟩

def classQ : squareclassNorm.ker := ⟨QuotientGroup.mk descentUnitQ, by simp⟩

theorem classP_ne_one : classP ≠ 1 := fun h =>
  field_nonsquare_class_ne_one _ descentUnitP_nonsquare (congrArg Subtype.val h)

theorem classQ_ne_one : classQ ≠ 1 := fun h =>
  field_nonsquare_class_ne_one _ descentUnitQ_nonsquare (congrArg Subtype.val h)

theorem classP_mul_classQ_ne_one : classP * classQ ≠ 1 := by
  intro h
  apply field_nonsquare_class_ne_one (descentUnitP * descentUnitQ)
    (by simpa only [NumberField.Units.coe_mul] using descentUnitProduct_nonsquare)
  rw [QuotientGroup.mk_mul]
  exact congrArg Subtype.val h

private theorem normSquareKernel_sq (x : squareclassNorm.ker) : x ^ 2 = 1 := by
  apply normSquareKernelEquiv.injective
  rw [map_pow, map_one, parity_sq]

/-- The explicit four classes, with each class appearing exactly once. -/
def explicitNormSquareClasses : Fin 4 ≃ squareclassNorm.ker := by
  let f : Fin 4 → squareclassNorm.ker := ![1, classP, classQ, classP * classQ]
  have hPQ : classP ≠ classQ := by
    intro h
    apply classP_mul_classQ_ne_one
    rw [← h, ← pow_two, normSquareKernel_sq]
  have hf : Function.Injective f := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp [f] at h ⊢ <;>
      (first | contradiction | exact (classP_ne_one h.symm).elim |
        exact (classQ_ne_one h.symm).elim | exact (classP_mul_classQ_ne_one h.symm).elim |
        exact (classP_ne_one h).elim | exact (classQ_ne_one h).elim |
        exact (classP_mul_classQ_ne_one h).elim | exact (hPQ h).elim |
        exact (hPQ h.symm).elim)
  letI : Finite squareclassNorm.ker := Nat.finite_of_card_ne_zero
    (norm_square_kernel_card.trans_ne (by decide))
  letI := Fintype.ofFinite squareclassNorm.ker
  exact Equiv.ofBijective f ⟨hf, (Finite.injective_iff_surjective_of_equiv
    (Fintype.equivOfCardEq (by
      rw [Fintype.card_fin, ← Nat.card_eq_fintype_card, norm_square_kernel_card]))).mp hf⟩

/-- A unit which becomes a square in the field was already a square of an integral unit. -/
theorem unit_squareclass_eq_one_iff (u : U) :
    (QuotientGroup.mk u : U ⧸ unitSquares) = 1 ↔ IsSquare (u : K) := by
  constructor
  · intro h
    by_contra hn
    exact field_nonsquare_class_ne_one u hn h
  · rintro ⟨z, hz⟩
    have hz' : z ^ 2 = (u : K) := by simpa [pow_two] using hz.symm
    let zi : 𝓞 K := ⟨z, IsIntegral.of_pow (by decide : 0 < 2)
      (hz'.symm ▸ (u : 𝓞 K).property)⟩
    have he : zi ^ 2 = (u : 𝓞 K) := Subtype.ext hz'
    have hi : IsUnit zi := (isUnit_pow_iff (by decide : (2 : ℕ) ≠ 0)).mp (he.symm ▸ u.isUnit)
    apply (QuotientGroup.eq_one_iff u).mpr
    refine ⟨hi.unit, Units.ext ?_⟩
    change (↑hi.unit : 𝓞 K) ^ 2 = (u : 𝓞 K)
    rw [hi.unit_spec, he]

/-- The global unit reduction with the norm-square condition retained. -/
theorem exists_norm_one_unit_of_even_valuations {a : K} (ha : a ≠ 0)
    (hn : IsSquare (Algebra.norm ℚ a))
    (he : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      Even (FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ a))) :
    ∃ (u : U) (b : K), unitNorm u = 1 ∧ b ≠ 0 ∧ a = (u : K) * b ^ 2 := by
  obtain ⟨u, b, hb, h⟩ := exists_unit_of_even_valuations ha he
  refine ⟨u, b, (unitNorm_isSquare_iff u).mp ?_, hb, h⟩
  obtain ⟨r, hr⟩ := hn
  let n := Algebra.norm ℚ b
  have hn0 : n ≠ 0 := fun hz => hb ((Algebra.norm_eq_zero_iff).mp hz)
  have hr' : Algebra.norm ℚ (u : K) * n ^ 2 = r * r := by
    simpa only [h, map_mul, map_pow] using hr
  refine ⟨r / n, ?_⟩
  apply (eq_div_iff (pow_ne_zero 2 hn0)).mpr at hr'
  rw [hr', pow_two, div_mul_div_comm]

/-- Every norm-square element with even finite valuations is in one of four field squareclasses. -/
theorem four_descent_representatives {a : K} (ha : a ≠ 0)
    (hn : IsSquare (Algebra.norm ℚ a))
    (he : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      Even (FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ a))) :
    ∃ (i : Fin 4) (b : K), b ≠ 0 ∧
      a = ((![1, descentUnitP, descentUnitQ, descentUnitP * descentUnitQ] i : U) : K) * b ^ 2 := by
  obtain ⟨u, b, hnorm, hb, h⟩ := exists_norm_one_unit_of_even_valuations ha hn he
  let x : squareclassNorm.ker := ⟨QuotientGroup.mk u, by simpa using hnorm⟩
  obtain ⟨i, hi⟩ := explicitNormSquareClasses.surjective x
  let v : U := ![1, descentUnitP, descentUnitQ, descentUnitP * descentUnitQ] i
  have hv : (explicitNormSquareClasses i).val = (QuotientGroup.mk v : U ⧸ unitSquares) := by
    fin_cases i <;> simp [v] <;> rfl
  have hclass : (QuotientGroup.mk v : U ⧸ unitSquares) = QuotientGroup.mk u :=
    hv.symm.trans (congrArg Subtype.val hi)
  have hquot : (QuotientGroup.mk (u / v) : U ⧸ unitSquares) = 1 := by
    rw [QuotientGroup.mk_div, hclass, div_self']
  obtain ⟨w, hw⟩ := (QuotientGroup.eq_one_iff (u / v)).mp hquot
  change w ^ 2 = u / v at hw
  have huw : u = v * w ^ 2 := by rw [hw, mul_comm v, div_mul_cancel]
  refine ⟨i, (w : K) * b, mul_ne_zero (NumberField.Units.coe_ne_zero w) hb, ?_⟩
  change a = (v : K) * ((w : K) * b) ^ 2
  rw [h, huw, NumberField.Units.coe_mul, NumberField.Units.coe_pow]
  ring

end CertifiedSelmer.Mathlib389.CubicField
