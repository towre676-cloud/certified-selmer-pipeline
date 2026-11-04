# Certified Selmer pipeline: trust-chain repair proposal

Audit date: November 4, 2026. Baseline: `76f7d2de615fb27cac21a0c571977d497972f86f` in `towre676-cloud/certified-selmer-pipeline`. PerfectPower comparison pinned to PR #15 head `698713a8b992b9ff5950f75322865a82329150c3`. This proposal has been implemented and tested locally. No remote branch, commit, PR, merge, release, or workflow dispatch was performed.

## Finding and exact mathematical target

**The existing receipts support no curve-specific Selmer, rank, Sha, regulator-enclosure, or analytic-rank theorem.** They support only statements about their own serialized values. The main receipt's historical SHA-256 check succeeds, its decimal endpoints are positive and strictly ordered, and its asserted Smith list is `[1,1]`. These are meaningful but limited facts. The sample under `receipts/` has a malformed/nonmatching root and different regulator endpoints; it is rejected rather than repaired automatically.

The intended claim `Selmer2inf_vanishes` was not defined mathematically: it was a theorem of `True`. Taken literally as vanishing of the full 2-primary infinite Selmer group, it is the wrong target for a rank-two curve. The Kummer exact sequence is

\[
0\to E(\mathbb Q)\otimes\mathbb Q_2/\mathbb Z_2
\to\operatorname{Sel}_{2^\infty}(E/\mathbb Q)
\to\Sha(E/\mathbb Q)[2^\infty]\to0.
\]

A proved Mordell–Weil rank of two would contribute two copies of `Q₂/Z₂` to that Selmer group. Vanishing of **Sha's 2-primary subgroup**, rather than vanishing of Selmer, is a plausible intended result. It is not presently proved by this repository.

A precise future target, for the model `E: y²+y=x³+x²−2x`, is

\[
\dim_{\mathbb F_2}\operatorname{Sel}_2(E/\mathbb Q)=2,
\qquad \operatorname{rank}E(\mathbb Q)=2,
\qquad \Sha(E/\mathbb Q)[2^\infty]=0.
\]

This is a target, not a result of this patch. The finite Kummer sequence gives

\[
0\to E(\mathbb Q)/2E(\mathbb Q)\to\operatorname{Sel}_2(E/\mathbb Q)
\to\Sha(E/\mathbb Q)[2]\to0.
\]

With no nonidentity rational two-torsion, two proved independent rational points and a proved Selmer dimension upper bound two would force rank two and make the Kummer image the entire Selmer group. The quotient would then be zero. A nonzero element of 2-power order would yield an element of order two by repeated doubling, so `Sha[2]=0` implies `Sha[2∞]=0`; this last implication requires no assumption that all of Sha is finite. Neither two independent classes nor the Selmer upper bound is supplied by the old receipt. Membership of two points in the curve alone does not prove their independence.

## What each layer actually establishes

| Layer | Baseline evidence | Correct interpretation / missing input |
|---|---|---|
| Data integrity | SHA-256 of JSON decoded and re-encoded through Python binary64 | Self-consistency of that decoded payload only; no signature, provenance, Merkle tree, or independent trusted root |
| Exact decimal facts | Originally parsed as floats | Now rational cross-products prove positive ordered literal endpoints; this is not containment of an arithmetic value |
| Numerical enclosure | Two interval pairs | No formula, precision ledger, directed rounding, truncation/tail bound, height matrix, point basis, or independent replay |
| Smith normal form | Bare `[1,1]` | No source matrix, change-of-basis witnesses, determinant checks, or identification of the represented arithmetic module |
| Exact Selmer calculation | None | Need a finite ambient descent space, exhaustive support bounds, all required places, exact local images and a proved identification with Selmer |
| Mordell–Weil conclusions | An asserted analytic rank | Need independent rational points, independence or independent Kummer classes, rank upper bound, and any basis/saturation claims separately justified |
| Formal proof | `True.intro` plus float definitions | Now nine narrow, axiom-free statements; no curve-specific Selmer theorem |
| Workflow success | Receipt rewriting, generation, compilation | Now explicitly limited to receipt facts and rejection tests; arithmetic requests fail |

The digest has an additional subtle limitation: two distinct decimal tokens can decode to the same binary64 value and therefore share this historical digest. A regression test demonstrates that limitation. The verifier retains that convention only to read historical evidence; it independently parses exact decimal fractions for formal literal facts. The raw receipt hash is recorded in the audit, and the pinned Git baseline identifies the reviewed source bytes. This is not a new authenticated receipt format. Future arithmetic certificates should use canonical exact integers/rational strings, domain-separated hashes, and an independently anchored digest or signature if authenticity is required. None of those measures would replace checking the arithmetic witnesses.

## Sage and receipt generation

The complete committed Sage file consists of loading the sample JSON and writing it as `receipts.json`. It constructs no curve, invokes no descent algorithm, computes no heights, regulator, Smith matrix, or L-value, and creates no proof witness. It is not evidence of a Sage arithmetic calculation. The proposed runner raises an explicit error and preserves the existing receipts until a genuine certificate-producing backend is implemented.

The old CI canonicalization step rewrote the embedded root whenever it differed from the computed value. That destroys the distinction between verification and issuance of a new digest. The replacement removes that step. A mismatch now fails. The sample remains unchanged as historical evidence, with a test asserting its rejection.

## Implemented proof architecture

1. **Untrusted producer.** A future Sage backend emits exact witnesses and labels numerical/analytic observations separately. Until then the old runner refuses to issue a certificate.
2. **Independent checker.** Strict JSON loading rejects duplicate keys, nonfinite values, wrong curve or prime, schema drift, booleans masquerading as integers, and invalid interval/list shapes. It never rewrites evidence. `--require-arithmetic` exits with status 2 because no arithmetic backend exists.
3. **Exact witness checks where available.** A small independent Smith checker verifies square integer matrices of dimension at most six, unimodularity of `U,V`, the identity `U A V=D`, positivity, and divisibility of diagonal entries. It is tested on valid and invalid witnesses. The legacy diagonal has no witnesses, so this checker is not used to certify it. This is exact linear algebra only, not an identification of an arithmetic cokernel.
4. **Limited formal translation.** The generator defaults to arithmetic scope and refuses the old receipt. Explicit `--scope receipt` emits exact rational endpoint data and literal facts. It validates before writing and replaces an output atomically only on success. Its output is named `Receipt_389a1_2.lean`; the former misleading Selmer proof file is removed.
5. **Kernel replay.** Lean 4.20.0 is pinned. No Mathlib dependency is introduced. The entire small library builds, and all nine current theorem declarations have individual transitive axiom reports. All nine reports are empty. The audit rejects missing reports, `sorryAx`, `Lean.ofReduceBool`, and arbitrary added axioms outside its allowlist. The audit list must be extended when adding new public theorems.
6. **Distinct publication states.** A successful workflow means receipt facts and trust-boundary tests passed. It cannot be reported as successful Selmer certification. Any later arithmetic workflow must require the separate arithmetic checker and genuinely instantiated arithmetic Lean theorems.

The generic theorem `quotient_trivial_of_exact_and_surjective` proves that a surjective quotient is trivial if its zero fibre is exactly a surjective Kummer image. Its functions, exactness equivalence, and surjectivity proofs are actual arguments. It is a reusable logical component, not a definition of elliptic-curve cohomology. Instantiating it with real Selmer and Sha objects remains necessary. `RationalInterval.WellFormed` and `Encloses` are separate predicates, so ordering endpoints cannot masquerade as proving enclosure.

## Strongest Lean statements actually replayed

| Declaration | What was proved |
|---|---|
| `Receipt389.reg_wellFormed` | Exact literal regulator endpoints have positive denominators and positive, ordered values |
| `Receipt389.lead_wellFormed` | The same structural fact for the leading-coefficient endpoints |
| `Receipt389.assertedSmith_identity` | The stored asserted list equals `[1,1]` |
| `Model389.point_zero`, `point_one` | `(0,0)` and `(1,0)` satisfy the explicit integer curve equation |
| `Model389.discriminant_eq`, `discriminant_nonzero` | The displayed Weierstrass discriminant expression equals 389 and is nonzero |
| `Model389.torsion_polynomial_mod_five` | The associated monic cubic has no root in the five residue classes |
| `quotient_trivial_of_exact_and_surjective` | The abstract exactness/surjectivity implication above |

The two points are not certified generators. The discriminant calculation is not a formal conductor calculation. The residue theorem is not itself a formal theorem identifying rational two-torsion: its arithmetic bridge has not been formalized in this dependency-free library. No Float-based inequality is used in these proofs.

## PerfectPower compatibility: a real obstruction

The inspected `TwoIsogenyPointMap.lean` defines `E(a,b)` by `y²=x(x²+a x+b)` with `b≠0` and `a²−4b≠0`. These models have the nonidentity rational order-two point `(0,0)`. PR #15's `elliptic_torsion_normalized_count` proves the actual-descent-image identity

\[
|\operatorname{im}\delta_\phi|\,|\operatorname{im}\delta_{\widehat\phi}|\,|E(\mathbb Q)[2]|
=4[E(\mathbb Q):2E(\mathbb Q)].
\]

Its rank variant retains a genuine free-plus-finite group decomposition, or an explicitly justified doubling-index formula. Its generic composition/kernel identities can be reused whenever their actual homomorphisms and exactness hypotheses are supplied. Local solubility does not automatically identify a Selmer group with the global descent image.

For 389a1 the model is instead `y²+y=x³+x²−2x`. Any nonidentity rational order-two point must have `y=−1/2`. Setting `t=4x` gives

\[
f(t)=t^3+4t^2-32t+16=0.
\]

By the rational root theorem a rational root of this monic integer polynomial is an integer dividing 16. The exact checker exhausts all ten signed divisors and finds no root. Independently the polynomial has residues `[1,4,1,3,1]` at `t=0,1,2,3,4` modulo five. Thus the curve has no nonidentity rational two-torsion. This mathematical argument and exact Python checks are new evidence, separate from the old receipts; the finite residue computation is also replayed in Lean.

A degree-two isogeny over Q has a rational nonidentity kernel point. Therefore 389a1 cannot be transported by a Q-isomorphism into PR #15's explicit two-isogeny family, or acquire a degree-two isogeny over Q through a coordinate change. Extending scalars changes the arithmetic problem and cannot be silently substituted. **Do not import PR #15 and claim it certifies 389a1.** A general full 2-descent using the cubic étale algebra is the appropriate direction here. PR #15 remains useful for a second regression curve with verified rational two-torsion and for generic group-counting infrastructure.

The PR source and its stated hypotheses were inspected at the pinned head. This audit did not freshly replay the much larger PerfectPower library; the local replay evidence reported here concerns this repaired repository only.

## Missing mathematical inputs and next implementation gates

- Define the intended arithmetic objects and target precisely: finite 2-Selmer dimension and 2-primary Sha vanishing, not full infinite-Selmer vanishing.
- Bind the curve label to explicit coefficients and a verified model/isomorphism. The original receipt has only a label.
- Produce full 2-descent data: the étale algebra, exhaustive squareclass support, relevant primes including 2 and infinity, exact local solubility/image certificates, and an independent checker proving completeness.
- Prove the needed independent Kummer classes or point independence. Saturation is a separate requirement for a claimed full Mordell–Weil basis or its regulator; it is not needed merely to combine a certified lower bound two with upper bound two.
- Formalize the Kummer exact sequence and instantiate the quotient theorem, or clearly document the remaining trusted mathematical theorem outside Lean. Do not insert it as an unproved axiom and call the result unconditional.
- If numerical BSD data remain a target, specify the normalized L-leading coefficient, period, Tamagawa factors, torsion denominator, point basis and regulator. Supply directed-rounding enclosures and explicit error bounds. Analytic rank requires exact vanishing of lower derivatives, not just a positive interval for an asserted leading derivative. Even a numerical BSD quotient of one would not prove Sha trivial without an applicable proved theorem.

## Validation and review scope

Local Python trust-chain tests pass, including rejection tests for corrupted/malformed inputs, rehashed fabricated arithmetic claims, stale-output protection, runner refusal, exact Smith witnesses, and unsafe/missing Lean axiom reports. The build and nine-declaration axiom audit pass with pinned Lean 4.20.0. The host's existing equivalent `/proc/self/exe` compatibility shim was needed to launch that compiler in this container; it changes no kernel or theorem. Standard elan installations do not require that shim.

The proposed GitHub workflow has not been run remotely. No Sage descent or rigorous numerical enclosure was executed; the runner intentionally fails. The artifacts under `audit/` record the local scope, source hashes, raw receipt hash, exact curve checks and logs. A reviewable patch and complete source snapshot accompany this report. Approval is requested only for creating a remote branch, committing this prepared repair and opening a PR; merging and release remain separate decisions.

## Primary sources

- [Baseline Sage runner](https://github.com/towre676-cloud/certified-selmer-pipeline/blob/76f7d2de615fb27cac21a0c571977d497972f86f/sage/selmer_ci_runner.sage)
- [Baseline verifier](https://github.com/towre676-cloud/certified-selmer-pipeline/blob/76f7d2de615fb27cac21a0c571977d497972f86f/python/verify_receipts.py), [generator](https://github.com/towre676-cloud/certified-selmer-pipeline/blob/76f7d2de615fb27cac21a0c571977d497972f86f/python/parse_certificate.py), and [workflow](https://github.com/towre676-cloud/certified-selmer-pipeline/blob/76f7d2de615fb27cac21a0c571977d497972f86f/.github/workflows/lean.yml)
- [PerfectPower counting source](https://github.com/towre676-cloud/perfectpower/blob/698713a8b992b9ff5950f75322865a82329150c3/PerfectPower/DescentCounting.lean) and [point-model source](https://github.com/towre676-cloud/perfectpower/blob/698713a8b992b9ff5950f75322865a82329150c3/PerfectPower/TwoIsogenyPointMap.lean)
- [Cremona's data-format explanation](https://wstein.org/Tables/cremona/INDEX.html), which explicitly identifies the 389a1 model and two table generators; table rank/generator claims are not adopted here as formal proofs.
- [Sage/eclib interface documentation](https://doc.sagemath.org/html/en/reference/libs/sage/libs/eclib/interface.html), distinguishing rank lower bounds, rank upper bounds, certainty and Selmer rank. A future Sage replay is additional computational evidence, not automatically a portable independent certificate.
