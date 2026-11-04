namespace CertifiedSelmer.Arithmetic389

/-- The descent-field polynomial; no Selmer group is defined in this module. -/
def cubic (x : Int) : Int := x^3 - x^2 - 9*x + 11

theorem norm_witness_two : -cubic 3 = -2 := by decide
theorem norm_witness_three : -cubic 2 = 3 := by decide

def cubicDiscriminant : Int := (-1)^2*(-9)^2 - 4*(-9)^3
  - 4*(-1)^3*11 - 27*11^2 + 18*(-1)*(-9)*11

theorem cubic_discriminant : cubicDiscriminant = 1556 := by decide
/-- Squaring the real Minkowski comparison gives this integer inequality. -/
theorem minkowski_comparison : 4*1556 < (81 : Nat)^2 := by decide

theorem no_root_mod_five :
    ∀ r : Fin 5, (r.val^3 + 4*r.val^2 + r.val + 1) % 5 ≠ 0 := by decide

theorem no_root_mod_seven :
    ∀ r : Fin 7, (r.val^3 + 6*r.val^2 + 5*r.val + 4) % 7 ≠ 0 := by decide

theorem two_nonsquare_mod_three : ∀ r : Fin 3, r.val^2 % 3 ≠ 2 := by decide

def affineCount (p : Nat) : Nat :=
  ((List.range p).flatMap fun (x : Nat) ↦
    (List.range p).filter fun (y : Nat) ↦
      ((y : Int)^2 + (y : Int) - (x : Int)^3 - (x : Int)^2 + 2*(x : Int)) % (p : Int) == 0).length

theorem count_mod_five : 1 + affineCount 5 = 9 := by decide
theorem count_mod_seven : 1 + affineCount 7 = 13 := by decide
theorem reduction_counts_bezout : (3 : Int)*9 - 2*13 = 1 := by decide

end CertifiedSelmer.Arithmetic389
