# A formal bridge to the actual curve

This optional Mathlib project defines `E : WeierstrassCurve ℚ` by `[0,1,1,-2,0]`. It proves its discriminant is 389, constructs the ellipticity instance, proves that its division cubic has no rational root, and proves:

```lean
lemma two_power_torsion_trivial (n : ℕ) (P : E.toAffine.Point)
    (h : (2^n) • P = 0) : P = 0
```

This is about actual rational points with Mathlib's group law. It is not merely a fact about integer residues, a numerical assertion, or a theorem of `True`. It is also not a statement about Sha: no Sha object is defined in this component.

The polynomial proof uses the integral-root theorem for a monic polynomial and an exhaustive obstruction modulo five. A point killed by doubling is fixed by negation, forcing `2*y+1=0`; substituting this into its actual curve equation contradicts the polynomial result. Induction proves the assertion for every power of two.

The seven audited declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`. They introduce no custom arithmetic axioms and no `sorryAx` or `Lean.ofReduceBool`. This differs from the 42 dependency-free declarations under `lean/`, whose axiom reports are empty.

Pinned versions: Lean 4.20.0 and Mathlib commit `c211948581bde9846a99e32d97a03f0d5307c31e`. To replay, install elan and run:

```bash
cd formal_mathlib
lake exe cache get Mathlib.RingTheory.Polynomial.RationalRoot Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point Mathlib.Tactic.ComputeDegree Mathlib.Tactic.NormNum Mathlib.Tactic.Ring Mathlib.Tactic.Linarith Mathlib.Tactic.LinearCombination
python3 replay.py
```

The script emits a compiled proof module using the pinned official compiler and then checks every declared axiom report. Evidence goes to `audit/mathlib389/`.

Local setup could not fetch ProofWidgets' web display release. The complete, source-keyed Mathlib cache was already present, so `lake exe cache unpack` supplied the unchanged compiled dependencies instead. The web display release is not part of these theorems. No mathematical source, compiler, kernel or axiom allowlist was patched. Ordinary network-enabled GitHub runners use the normal cache command above. The host also needed the previously recorded equivalent `/proc/self/exe` launcher shim; ordinary elan installations do not.

Remaining: the cubic field's class-number and unit arguments, actual Kummer/Selmer objects and exactness, the rank computation, and the height/analytic identifications have not yet been joined into an end-to-end formal proof of the paper-level conclusions.
