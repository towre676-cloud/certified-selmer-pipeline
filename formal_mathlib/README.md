# Formal bridges for 389a1

## Rational curve

This optional Mathlib project defines `E : WeierstrassCurve ℚ` by `[0,1,1,-2,0]`. It proves its discriminant is 389, constructs the ellipticity instance, proves that its division cubic has no rational root, and proves:

```lean
lemma two_power_torsion_trivial (n : ℕ) (P : E.toAffine.Point)
    (h : (2^n) • P = 0) : P = 0
```

This is about actual rational points with Mathlib's group law. It is not merely a fact about integer residues, a numerical assertion, or a theorem of `True`. It is also not a statement about Sha: no Sha object is defined in this component.

The polynomial proof uses the integral-root theorem for a monic polynomial and an exhaustive obstruction modulo five. A point killed by doubling is fixed by negation, forcing `2*y+1=0`; substituting this into its actual curve equation contradicts the polynomial result. Induction proves the assertion for every power of two.

## Cubic field and integral arithmetic

[CubicField389.lean](CubicField389.lean) defines the number field
`K = AdjoinRoot g` over `ℚ` for `g(T) = T³ − T² − 9T + 11`. The shift
`g(T+1)` is Eisenstein at 2. Gauss's lemma and translation give irreducibility
over `ℚ`. The identity `F(2T−2) = 8g(T)` yields an algebra equivalence from
`ℚ[T]/(F)` to `K`, taking the division root to `θ = 2β−2`.

The existing `CubicZ` coordinates map injectively into `K`. Their image is
`ℤ[β]`, and the map respects multiplication and integer scaling. Mathlib's
field norm agrees with the existing coordinate determinant for every triple.
The trace pairing of `(1, β, β²)` has determinant 1556, and the division-root powers have discriminant 99584. The existing finite
cover witnesses now give actual equations in `K`.

The shifted Eisenstein polynomial proves that `ℤ[β]` is saturated at 2 in
the integral closure. The power-basis discriminant then implies that
`389z ∈ ℤ[β]` for every algebraic integer `z`. Since 389 is invertible
modulo eight, every algebraic integer has a power-order representative modulo
eight. The existing finite obstruction for `unitP` therefore gives the
modulo-eight nonsquare obstruction in the actual ring of integers, and rules
out a square root of `unitP` in `K`.

## Replay and scope

The axiom audit allows only `propext`, `Classical.choice`, and `Quot.sound`.
The dependency-free declarations under `lean/` are still separately audited
against an empty allowlist. The replay also checks focused Lean regression
examples that reuse the existing norm, normalization, and cover witnesses.

Pinned versions are Lean 4.20.0 and Mathlib commit
`c211948581bde9846a99e32d97a03f0d5307c31e`. Install elan and run:

```bash
cd formal_mathlib
lake exe cache get \
  Mathlib.RingTheory.Polynomial.RationalRoot \
  Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point \
  Mathlib.Algebra.Polynomial.SpecificDegree Mathlib.Algebra.Polynomial.Taylor \
  Mathlib.NumberTheory.NumberField.Basic Mathlib.RingTheory.Adjoin.PowerBasis \
  Mathlib.RingTheory.Discriminant Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral \
  Mathlib.RingTheory.Polynomial.GaussLemma Mathlib.Tactic.ComputeDegree \
  Mathlib.Tactic.NormNum Mathlib.Tactic.Ring Mathlib.Tactic.Linarith \
  Mathlib.Tactic.LinearCombination Mathlib.Tactic.FinCases Mathlib.Tactic.IntervalCases
python3 replay.py
```

The replay emits proof modules, runs the regression examples, and records
transitive axiom reports and source hashes in `audit/mathlib389/`.

Remaining obligations include maximality at 389 and the field discriminant,
the class-number and full unit arguments, local-field squareclass and
local-image theorems, and the Kummer and Selmer objects and exactness needed
for the rank and 2-primary Tate–Shafarevich conclusions.
