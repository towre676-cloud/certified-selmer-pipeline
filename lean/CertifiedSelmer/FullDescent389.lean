/- Exact cubic-algebra witnesses for full descent on 389a1.
   Finite proofs are kernel-replayed; the number-field, local-field and
   cohomological identifications remain in the conventional written proof. -/
namespace CertifiedSelmer.FullDescent389

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

structure CubicZ where
  a : Int
  b : Int
  c : Int
  deriving DecidableEq, Repr

def one : CubicZ := ⟨1, 0, 0⟩
def zero : CubicZ := ⟨0, 0, 0⟩
def scale (n : Int) (x : CubicZ) : CubicZ := ⟨n*x.a, n*x.b, n*x.c⟩

/-- Coordinates in Z[β], β³ = β² + 9β - 11. -/
def mul (x y : CubicZ) : CubicZ :=
  let t₀ := x.a*y.a
  let t₁ := x.a*y.b + x.b*y.a
  let t₂ := x.a*y.c + x.b*y.b + x.c*y.a
  let t₃ := x.b*y.c + x.c*y.b
  let t₄ := x.c*y.c
  ⟨t₀ - 11*t₃ - 11*t₄, t₁ + 9*t₃ - 2*t₄, t₂ + t₃ + 10*t₄⟩

def sq (x : CubicZ) := mul x x

def det3 (x y z : CubicZ) : Int :=
  x.a*(y.b*z.c-y.c*z.b) - y.a*(x.b*z.c-x.c*z.b) + z.a*(x.b*y.c-x.c*y.b)

def norm (x : CubicZ) : Int := det3 x (mul x ⟨0,1,0⟩) (mul x ⟨0,0,1⟩)

/-- A rational square, allowing every denominator in the β basis.
    This is deliberately stronger than an integral-square predicate. -/
def IsRationalSquare (x : CubicZ) : Prop :=
  ∃ (z : CubicZ) (d : Nat), 0 < d ∧ sq z = scale ((d : Int)^2) x

/-- Equality of nonzero rational squareclasses, written with cleared denominators. -/
def SameRationalSquareclass (x y : CubicZ) : Prop :=
  x ≠ zero ∧ y ≠ zero ∧ ∃ (z : CubicZ) (d : Nat),
    z ≠ zero ∧ 0 < d ∧ mul x (sq z) = scale ((d : Int)^2) y

/-- A rational point on the cubic norm-cover equations δz² = X-θ.
    This is a witness predicate, not an asserted Selmer completeness theorem. -/
def NormCoverWitness (δ : CubicZ) (X Y : Int) : Prop :=
  Y^2 = X^3 + 4*X^2 - 32*X + 16 ∧
  ∃ (z : CubicZ) (d : Nat), 0 < d ∧
    mul δ (sq z) = scale ((d : Int)^2) ⟨X+2,-2,0⟩

def pi : CubicZ := ⟨-3,1,0⟩
def alphaP : CubicZ := ⟨2,-2,0⟩
def alphaQ : CubicZ := ⟨6,-2,0⟩
def alphaR : CubicZ := ⟨-6,-2,0⟩
def unitP : CubicZ := ⟨1194,-552,-305⟩
def unitQ : CubicZ := ⟨-125,58,32⟩

theorem norm_pi : norm pi = -2 := by decide
theorem norm_alphaP : norm alphaP = 16 := by decide
theorem norm_alphaQ : norm alphaQ = 16 := by decide
theorem norm_unitP : norm unitP = 1 := by decide
theorem norm_unitQ : norm unitQ = 1 := by decide
theorem normalize_P : mul (sq (sq pi)) unitP = alphaP := by decide
theorem normalize_Q : mul (sq (sq pi)) unitQ = alphaQ := by decide
theorem chord_square : mul (mul alphaP alphaQ) alphaR = scale 16 one := by decide

theorem cover_P : NormCoverWitness alphaP 0 4 := by
  constructor
  · decide
  · exact ⟨one, 1, by decide, by decide⟩

theorem cover_Q : NormCoverWitness alphaQ 4 4 := by
  constructor
  · decide
  · exact ⟨one, 1, by decide, by decide⟩

/-- The product class has the rational cover witness z=alphaR/4 at P+Q. -/
theorem cover_product : NormCoverWitness (mul alphaP alphaQ) (-8) (-4) := by
  constructor
  · decide
  · exact ⟨alphaR, 4, by decide, by decide⟩

end CertifiedSelmer.FullDescent389

namespace CertifiedSelmer.FullDescent389

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

/-- Coordinate congruence in the actual integral cubic basis. -/
def Congruent (n : Int) (x y : CubicZ) : Prop :=
  (x.a-y.a) % n = 0 ∧ (x.b-y.b) % n = 0 ∧ (x.c-y.c) % n = 0

instance (n : Int) (x y : CubicZ) : Decidable (Congruent n x y) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- No element of O_K/8O_K squares to uP. This is a finite obstruction;
    its implication for local squares uses the maximal-order bridge. -/
theorem unitP_not_square_mod_eight :
    ∀ a b c : Fin 8,
      ¬ Congruent 8 (sq ⟨(a.val : Int), (b.val : Int), (c.val : Int)⟩) unitP := by
  decide

/-- Together with Hensel's lemma, this proves equality of the two dyadic classes. -/
theorem product_square_mod_eight :
    Congruent 8 (sq ⟨1,3,1⟩) (mul unitP unitQ) := by decide

theorem dyadic_root_unit_norm : norm ⟨1,3,1⟩ % 2 = 1 := by decide

def residue (x : CubicZ) (r : Int) : Int := x.a + x.b*r + x.c*r^2

theorem Q_residue_mod_three : residue alphaQ 2 % 3 = 2 := by decide

theorem three_nonsquare_residue :
    ∀ a : Fin 3, (a.val : Int)^2 % 3 ≠ 2 := by decide

theorem Q_square_linear_389 :
    ((77 : Int)^2 - residue unitQ (-30)) % 389 = 0 := by decide

theorem Q_square_ramified_389 :
    ((43 : Int)^2 - residue unitQ 210) % 389 = 0 := by decide

theorem P_nonsquare_ramified_389 :
    (residue unitP 210)^194 % 389 = 388 := by decide

def divisionCubic (x : Int) := x^3 + 4*x^2 - 32*x + 16

theorem double_root_389_value : divisionCubic 29 = 389*69 := by decide

theorem double_root_389_derivative :
    3*(29 : Int)^2 + 8*29 - 32 = 389*7 := by decide

/-- Cleared-denominator evaluation: 1000³ g(t/1000). -/
def scaledCubic (t : Int) := t^3 - 1000*t^2 - 9000000*t + 11000000000

theorem three_real_root_brackets :
    scaledCubic (-3081) < 0 ∧ 0 < scaledCubic (-3080) ∧
    0 < scaledCubic 1270 ∧ scaledCubic 1271 < 0 ∧
    scaledCubic 2809 < 0 ∧ 0 < scaledCubic 2810 := by decide

/-- A rational, denominator-four equivalence of nonzero squareclasses. -/
theorem product_class_equals_R : SameRationalSquareclass (mul alphaP alphaQ) alphaR := by
  refine ⟨by decide, by decide, alphaR, 4, by decide, by decide, ?_⟩
  decide

end CertifiedSelmer.FullDescent389
