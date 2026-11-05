# 389a1: actual-curve formalization and four odd-primary Sha bounds

November 4, 2026. Baseline: PR #1 head `1be3c5939ed942d82377daa697227e8452eb5747`, preserving the concurrent full-descent witness integration. Both GitHub runs for its preceding commit `7ca095e` succeeded. The changes described here are a new local proposal; they have not been committed, merged or run in GitHub Actions.

## Result and evidence boundary

The project now has two substantive advances beyond the written proof and numerical checks, while preserving the concurrent portable finite-witness work.

1. A separate pinned Mathlib project proves a curve-level theorem: if a rational point of 389a1 is killed by any power of two, it is the identity. The proof uses actual `WeierstrassCurve ℚ` and its point group, so the earlier residue-only gap is closed for this statement.
2. A fresh pinned Sage/PassageMath replay returns a proved upper bound of one for each of the 5-, 7-, 11- and 13-primary parts of Sha. This uses the implemented Stein–Wuthrich/Kato upper-bound theorem, not an inference from a floating-point or p-adic BSD approximation.

These statements concern different groups: absence of rational two-power torsion is a theorem about E(Q); the prime-primary Sha bounds concern obstructions to the local-to-global principle. Neither should be substituted for the other.

| Claim | Current evidence |
|---|---|
| No nonidentity point in `E(Q)[2^infinity]` | New complete Mathlib proof, seven audited declarations using only the three standard Lean axioms |
| Rank two and full basis `(0,0),(1,0)` | Existing written arithmetic proof with exact and ball-arithmetic checks; not yet end-to-end formal |
| `Sha[2^infinity]=0` | Existing written full 2-descent argument; not yet end-to-end formal |
| `Sha[p^infinity]=0`, p=5,7,11,13 | New theorem-backed CAS replay with recorded applicability and precision checks |
| Full Sha triviality or finiteness | Not established by this work |
| Full BSD leading-term identity | Not established by this work |
| Exact Sha group defined in Lean | Not yet constructed here |

## The four odd-prime computations

All calls use the explicit rational model `[0,1,1,-2,0]`, with proof flags enabled. Rank and generators are recomputed with `algorithm='pari'`, `proof=True`, `use_database=False`; no asserted rank or point basis is inserted into Sage. The run uses PassageMath 10.8.13 wheels for schemes, eclib, symbolics and PARI. Implementation-file and runner hashes accompany the receipt.

| p | a_p | Good ordinary | Backend residual surjectivity | Proved exponent bound | Higher-precision p-adic ratio |
|---:|---:|:---:|:---:|---:|---|
| 5 | −3 | yes | yes | 0 | `1 + O(5^2)` |
| 7 | −5 | yes | yes | 0 | `1 + O(7^2)` |
| 11 | −4 | yes | yes | 0 | `1 + O(11^2)` |
| 13 | −3 | yes | yes | 0 | `1 + O(13^2)` |

The function `p_primary_bound(p)` returns an exponent e such that `#Sha[p^infinity] <= p^e`, with finiteness part of the theorem-backed conclusion. Each returned e is zero, so these four primary subgroups are trivial.

The nearby routine `an_padic` is documented as a conjectural equality for the order. A unit value from that routine alone is not a proof. We record it at default and higher precision only as the numerical ingredient used and cross-checked inside the proved upper-bound algorithm. The inference comes from the upper-bound theorem after checking its hypotheses. We do not infer an exact BSD identity from the ratio being a unit.

This remains a trusted computer-algebra layer. It is not a portable independent proof certificate, a formal Lean theorem, or an audit of all internal modular-symbol and p-adic height algorithms. The receipt explicitly states those limits. In particular, normalizations and precision correctness are delegated to the pinned implementation and its cited theory; a source hash alone does not prove them.

### Additional finite witnesses for applicability

The replay independently counts points over small finite fields to produce irreducible Frobenius characteristic polynomials. For each p it finds a good q different from p for which `a_q^2−4q` is a nonsquare modulo p:

| p | q | a_q | Discriminant modulo p |
|---:|---:|---:|---:|
| 5 | 3 | −2 | 2 |
| 7 | 2 | −2 | 3 |
| 11 | 2 | −2 | 7 |
| 13 | 3 | −2 | 5 |

An invariant rational line in the residual representation would make every Frobenius characteristic polynomial split, so these witnesses establish residual irreducibility. Also, at the split multiplicative prime 389, `v_389(Delta_min)=1`. For these p different from 389 this gives a nontrivial transvection in residual inertia. The standard two-dimensional subgroup argument for p>=5, together with the cyclotomic determinant, yields full residual image. Sage separately checks residual surjectivity; the finite witnesses make the applicability ledger more transparent.

These are not independent replacements for the full p-adic upper-bound computation. They address the residual-image hypothesis only.

### The first missing small prime

A direct trial of the same backend at 3 raises

```
NotImplementedError: p (=3) must be at least 5
```

The runner records this rejection and never converts it to a zero bound. An explicit guard also rejects unreviewed primes before importing the backend. A genuine 3-descent or a separately justified implementation of a theorem applicable at 3 remains necessary. A software limitation at 3 is not evidence for nontrivial 3-primary Sha.

Even proving the 3-primary part trivial would leave unboundedly many primes outside this replay. A theorem limiting all possible prime divisors, or some general argument handling the remaining primes, is still missing. There is no deduction from a finite list of vanishing primary parts to finiteness or triviality of all Sha.

## The seven new formal declarations

`formal_mathlib/Curve389.lean` defines the actual curve E and the integral monic division cubic

`X^3 + 4 X^2 - 32 X + 16`.

The formal chain is:

- Monicity plus the integral-root theorem turns a hypothetical rational root into an integer root.
- Reduction to `ZMod 5`, with exhaustive checking of five residues, excludes that root.
- The actual curve equation excludes an affine point fixed by negation.
- The actual Weierstrass discriminant is proved equal to 389, yielding an ellipticity instance.
- A point killed by 2 must be fixed by negation; hence it is the identity.
- Induction proves that a point killed by `2^n` must be the identity for every n.

The final statement is

```lean
lemma two_power_torsion_trivial (n : ℕ) (P : E.toAffine.Point)
    (h : (2^n) • P = 0) : P = 0
```

All seven transitive axiom reports are exactly contained in `{propext, Classical.choice, Quot.sound}`. No arithmetic axiom, `sorryAx`, or `Lean.ofReduceBool` is accepted. The concurrently integrated dependency-free library now contains 42 axiom-free declarations, including 23 additional finite descent facts. This extension preserves those files and adds the seven actual-curve declarations. Thus 49 declarations are audited in two clearly distinguished projects; they are not all axiom-free.

The new formal result closes the rational-root/actual-point-group step. It does not formally identify a Selmer group, prove a cubic class number, or establish a rank or Sha theorem. The generic receipt-to-proof interface continues to fail closed for those claims.

## Reproduction and proposed integration

Combined local validation passed 38 Python tests, the 42-declaration core replay with empty axiom lists, and the seven-declaration Mathlib replay using only the standard axiom allowlist. The ordinary regression suite runs without importing Sage. The three new guard tests check rejection of unreviewed, empty or duplicate prime selections and validate the Frobenius nonsquare witnesses by explicit square enumeration, independently of Euler's criterion. The odd-primary replay runs in a fresh process so its PARI runtime is not mixed with the separate cypari library used by the earlier tests.

```bash
python3 -m pip install -r arithmetic/requirements.txt
python3 -m unittest discover -s tests -v
python3 -m pip install -r arithmetic/requirements-odd-primary.txt
python3 arithmetic/odd_primary_replay.py
```

For the Mathlib component, follow `formal_mathlib/README.md`. It pins both compiler and Mathlib, emits a compiled proof module and audits every declared transitive axiom list. The proposed additional workflow has separate jobs for this formal replay and for the theorem-backed CAS computation. Those workflows have not yet run remotely for these new changes.

Proposed consequential operation after review: add this prepared follow-up to the existing PR branch and update the PR description. No merge or release is proposed.

## Primary sources

- William Stein and Christian Wuthrich, [Algorithms for the arithmetic of elliptic curves using Iwasawa theory](https://wstein.org/papers/mcom2649-iwasawa-alg.pdf), Math. Comp. 82 (2013), 1757–1792. This is the cited source for the implemented upper-bound algorithm, including its precision analysis.
- [Official Sage Sha documentation](https://doc.sagemath.org/html/en/reference/arithmetic_curves/sage/schemes/elliptic_curves/sha_tate.html), distinguishing `an_padic`, `p_primary_bound`, and `p_primary_order`.
- [Official Sage tutorial](https://doc.sagemath.org/html/en/thematic_tutorials/explicit_methods_in_number_theory/elliptic_curves.html), which already gives the p=5,7 examples for 389a1 and explicitly separates these from full Sha finiteness. These are known arithmetic facts being reproduced for the pipeline, not new number-theoretic discoveries.
- [Mathlib rational-root theorem at the pinned revision](https://github.com/leanprover-community/mathlib4/blob/c211948581bde9846a99e32d97a03f0d5307c31e/Mathlib/RingTheory/Polynomial/RationalRoot.lean) and [actual affine point groups](https://github.com/leanprover-community/mathlib4/blob/c211948581bde9846a99e32d97a03f0d5307c31e/Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean).
