namespace CertifiedSelmer.Model389

def OnCurve (x y : Int) : Prop := y^2 + y = x^3 + x^2 - 2*x

theorem point_zero : OnCurve 0 0 := by unfold OnCurve; decide
theorem point_one : OnCurve 1 0 := by unfold OnCurve; decide

/-- Weierstrass discriminant from b₂=4, b₄=-4, b₆=1, b₈=-3. -/
def discriminant : Int := -(4^2)*(-3) - 8*(-4)^3 - 27*1^2 + 9*4*(-4)*1
theorem discriminant_eq : discriminant = 389 := by decide
theorem discriminant_nonzero : discriminant ≠ 0 := by decide

/-- Finite obstruction only; the bridge to rational two-torsion is not formalized. -/
theorem torsion_polynomial_mod_five :
    ∀ r : Fin 5, (r.val^3 + 4*r.val^2 + 3*r.val + 1) % 5 ≠ 0 := by decide

end CertifiedSelmer.Model389
