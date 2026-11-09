# Full 2-descent on 389a1: exact witnesses and the arithmetic theorem

November 4, 2026. Integrated follow-up based on certified-selmer-pipeline PR #1 at `7ca095e71ccbaf3dbb81d0aebe101c1c77ed7036`, preserving its prior arithmetic, numerical and saturation work. The earlier trust-repair baseline was independently reconstructed and its 28 blobs matched GitHub hashes; the current working repository was checked out at the newer pinned head.

## Result and trust boundary

For

\[
E:\quad y^2+y=x^3+x^2-2x,
\]

the conventional mathematical argument below establishes

\[
\dim_{\mathbf F_2}\operatorname{Sel}_2(E/\mathbf Q)=2,
\quad \operatorname{rank}E(\mathbf Q)=2,
\quad \Sha(E/\mathbf Q)[2^\infty]=0.
\]

The points P=(0,0), Q=(1,0) have independent Kummer classes. They generate E(Q)/2E(Q), and their subgroup has finite odd index in E(Q). This descent alone does **not** establish index one or a full Mordell–Weil basis. Coprime good-reduction counts also prove that E(Q) has trivial torsion.

The finite inputs are freshly checked using Python's standard library, without Sage, PARI, numerical roots, regulator estimates, or a supplied class-number result. The checker is not an implementation of all the mathematical theory: the checker verifies finite arithmetic inputs to the conventional argument. The new module `CertifiedSelmer.FullDescent389` contains actual arithmetic predicates and **23 kernel-replayed finite witness proofs**. It is imported into the default library and included in its axiom audit. All **42 audited declarations** have empty transitive axiom lists under freshly installed Lean 4.20.0. The optional [Mathlib bridge](../formal_mathlib/README.md) identifies the cubic algebra with the actual number field, checks its power-basis discriminants, and lifts the finite modulo-eight obstruction to the ring of integers. The local-image and cohomological steps of this descent remain conventional proofs.

No fresh analytic-rank, height, period, regulator, BSD or full-Sha theorem is asserted here. The previously saved arithmetic bundle includes work on those distinct topics; none is needed for this descent or substituted for it.

## 1. Integral cubic algebra and maximal order

Set X=4x, Y=8y+4. Then Y²=F(X), with

\[
F(T)=T^3+4T^2-32T+16.
\]

Let g(T)=T³−T²−9T+11, K=Q(β), g(β)=0, and θ=2β−2. The exact identity F(2T−2)=8g(T) identifies K with the full 2-division cubic algebra. The checker verifies multiplication in the basis (1,β,β²), using β³=β²+9β−11, and recomputes norms as determinants of multiplication matrices. The trace pairing is

\[
\begin{pmatrix}3&1&19\\1&19&-5\\19&-5&155\end{pmatrix},
\quad\det=1556=4\cdot389.
\]

The shifted polynomial g(T+1)=T³+2T²−8T+2 is Eisenstein at 2. Consequently g is irreducible over Q and over Q₂; at 2, K has one prime with ramification degree three and residue degree one. The extension is tame, since 3 is prime to residue characteristic 2, so its local field discriminant exponent is two. This equals the exponent in disc(g). No odd prime can divide the order index: 389 is the only possible one, and its discriminant exponent is one. The discriminant-index identity therefore proves O_K=Z[β] and disc(K)=1556. In contrast disc(F)=99584=64·1556; disc(F) is not the field discriminant.

Three disjoint sign-changing rational brackets

(-3081/1000,−3080/1000), (1270/1000,1271/1000), (2809/1000,2810/1000)

exhaust the roots of a cubic. Thus K is totally real. This gives rigorous embedding and sign information without approximate root computations.

## 2. Class number one with exhaustive finite support

Minkowski's theorem gives each ideal class an integral ideal of norm at most (2/9)√1556<9; the last inequality is the exact integer comparison 6224<6561. Therefore only prime ideals of norm less than nine need consideration.

| Rational prime | Factorization information | Small prime ideal witness |
|---|---|---|
| 2 | Totally ramified, one residue-degree-one prime | N(β−3)=−2 |
| 3 | g=(T+1)(T²+T+2), irreducible quadratic | N(β−2)=3 for the norm-three prime |
| 5 | Irreducible cubic | Smallest prime norm 125 |
| 7 | Irreducible cubic | Smallest prime norm 343 |

The second prime above 3 has norm nine and is outside the bound. The norm-two and norm-three witnesses generate the respective prime ideals, since their principal ideals have exactly those absolute norms. All possible prime factors of a Minkowski representative are principal. Hence Cl(K)=0. This is an unconditional class-number proof, independent of GRH or a CAS class-group routine.

## 3. Local valuation lemma and the finite squareclass group

Use the standard full 2-descent injection

Sel₂(E/Q) → ker(N:K×/K×² → Q×/Q×²),

whose Kummer image away from local two-torsion is [X−θ]. The norm identity is N(X−θ)=F(X)=Y². Local solubility means that a Selmer class agrees with a local Kummer image at each place. We now show that all its finite ideal valuations are even.

At odd p other than 389, F is integral and étale. If X is integral, only the single simple degree-one factor whose root reduces to X can contribute to X−θ; all other factors are units. The square norm forces that valuation to be even. If X is not integral, v_p(F(X))=3v_p(X) is even, so v_p(X) is even and each factor valuation e·v_p(X) is even.

At p=389 the exact factorization and values are

\[
F(T)\equiv(T+62)(T-29)^2\pmod{389},
\quad F(29)=389\cdot69,\quad F'(29)=389\cdot7.
\]

Hensel factorization separates a linear factor and a ramified quadratic factor. In the quadratic factor θ−29 has normalized valuation one: the linear factor evaluated at 29 is a unit, and the quadratic factor's norm value has p-valuation one. If integral X reduces to 29, X−θ has valuation one in this factor, while its linear factor is a unit. Its total norm would have odd p-valuation, impossible for Y². If X reduces to the simple root, only that linear factor contributes, and its valuation is even. Otherwise all factors are units. Nonintegral X is treated as before. The rational local two-torsion at the simple root follows either from the extended Kummer formula or continuity of local squareclasses; it introduces no odd valuation.

At p=2 there is just one prime of K, of residue degree one. For any representative with square norm, the formula v₂(Nα)=Σ f_q v_q(α) immediately forces its valuation to be even. This argument does not incorrectly apply an odd-residue-characteristic lemma at 2.

Thus (α) is a square fractional ideal at every finite prime. Since the class group is trivial, α can be divided by a square to obtain a unit. Dirichlet's unit theorem gives O_K×≅{±1}×Z², so its unit squareclass group has dimension three. Because N(−1)=−1, its norm-square kernel has dimension two, hence order four. Therefore #Sel₂≤4.

This proves completeness of the finite support: one may initially use primes above {2,389}; the local and norm arguments remove every odd valuation, leaving the unramified unit squareclasses. There is no unexplained S-unit basis or unverified unit-saturation assertion.

## 4. Independent global classes, explicit units and covers

The checker verifies P=(0,0), Q=(1,0), R=P+Q=(−2,−1), with representatives

αP=2−2β, αQ=6−2β, αR=−6−2β.

Each has norm 16. The scaled points are (0,4), (4,4), (−8,−4). The chord identity is αPαQαR=16. Consequently [αR]=[αPαQ]; more explicitly αPαQ(αR/4)²=αR. This supplies a rational norm-cover witness for the product class as well as the trivial z=1 witnesses for P and Q. These are equations for the usual full-descent norm-cover presentation δz²=X−θ; they do not assert that arbitrary locally soluble covers have rational points.

With π=β−3 the checker verifies

\[
α_P=π^4 u_P,\quad u_P=1194-552β-305β^2,
\qquad
α_Q=π^4 u_Q,\quad u_Q=-125+58β+32β^2,
\quad N(u_P)=N(u_Q)=1.
\]

The real signs of αP are (+,−,−); αQ has signs (+,+,+). Thus αP and αPαQ are nonsquares. At the simple prime (3,β−2), αQ reduces to 2, a nonzero nonsquare in F₃. A local square unit has square residue, so αQ is also a nonsquare. This proves that [1], [αP], [αQ], [αPαQ] are distinct. The unit normalizations divide by a square and preserve their classes.

Dirichlet's dimension bound now also proves that the eight classes (−1)^e uP^a uQ^b, e,a,b∈{0,1}, exhaust the entire unit squareclass group: the first factor is separated by norm sign, and the other two are independent. The four classes with e=0 exhaust its norm-square kernel. An exact fundamental-unit computation is unnecessary.

## 5. Explicit local conditions on the four candidates

Use bit 1 for the specified nontrivial local basis class. On P,Q the local restriction maps are:

| Place | P | Q | Explicit witness |
|---|---:|---:|---|
| R | 1 | 0 | Signs (+,−,−) and (+,+,+) |
| Q₂ | 1 | 1 | uPuQ≡(1+3β+β²)² mod 8; uP is not a square mod 8 |
| Q₃₈₉ | 1 | 0 | Q square residues in both factors; P nonsquare in the ramified factor |

For Q₂, the checker enumerates all 8³=512 elements of O_K/8O_K. There is no square root of uP modulo 8. Any local square root of a unit would be integral, so this is a valid obstruction. Conversely z=1+3β+β² is a unit and z²≡uPuQ mod 8. The quotient uPuQ/z² lies in 1+8O_{K₂}, hence is a square by Hensel's lemma. Thus P and Q have the same nontrivial local class.

For Q₃₈₉, the residue values of β in the linear and ramified quadratic factors are −30 and 210. The unit uQ has residues 94=77² and 293=43² modulo 389. Nonzero square residues lift in both local factors, since their residue characteristic is odd. The ramified-factor residue of uP is 371 with 371^194≡−1 mod 389, so P is nontrivial. The usual local image cardinalities are two at each of these three places: E[2](Q₂)=0 gives #E(Q₂)/2=2, the factorization at 389 gives one rational nonzero two-torsion point and index two, and the real locus has two components.

All four global candidates satisfy every local condition because they are represented by O, P, Q and P+Q. This supplies local membership everywhere, including all good primes, without an infinite list of local computations. The upper bound in Section 3 independently excludes every other candidate. The table describes restrictions of global classes; it is not a list of three equations setting those bits to zero. Local solubility allows the indicated nonzero Kummer images.

## 6. Rank and Sha through the finite exact sequence

There are now four distinct actual global Kummer classes, so

4≤#E(Q)/2E(Q)≤#Sel₂(E/Q)≤4.

The irreducible 2-division cubic proves E(Q)[2]=0. Mordell–Weil finite generation then gives #E(Q)/2E(Q)=2^rank, hence rank two. The finite Kummer sequence

0→E(Q)/2E(Q)→Sel₂(E/Q)→Sha(E/Q)[2]→0

forces Sha[2]=0. Any nonzero element of finite 2-power order produces an element of order two by repeated doubling. Therefore Sha[2∞]=0, with **no assumption that the full Sha group is finite**. The infinite Selmer group is consequently isomorphic to (Q₂/Z₂)², rather than zero.

For completeness, exhaustive counts give #E(F₅)=9 and #E(F₇)=13. Good reduction injects rational torsion of order prime to the residue characteristic. Using the two primes removes the exceptional 5- and 7-primary possibilities as well, and their coprime counts imply trivial rational torsion. The descent proves P,Q generate modulo two and have odd index, but makes no saturation claim at odd primes.

## 7. Replay, review and remaining formal obligations

From the repository root:

```bash
python3 arithmetic/full_descent_389.py
python3 -O arithmetic/full_descent_389.py
python3 -m unittest discover -s tests -v
# With the pinned Lean 4.20.0 toolchain:
python3 python/audit_lean.py
```

Fresh validation: all 35 tests passed (the current branch's 23 trust-boundary, arithmetic and numerical tests plus 12 new descent tests). Deliberately corrupted curves, fields, points, cover witnesses, units, local square roots, root brackets, schemas and Minkowski data are rejected. Duplicate JSON keys and boolean-as-integer substitutions are rejected. Validation remains active under Python optimization. An optional independent Sympy resultant/polynomial replay agrees with all sampled quotient multiplication and norm computations; Sympy is not required by the portable checker.

The integrated Lean module defines rational-square and rational-squareclass predicates with explicit denominator quantifiers, a genuine cubic norm-cover witness predicate, and 23 finite witness theorems. The latter include the complete 512-case modulo-eight obstruction, local square witnesses at 389, real root-bracket signs and a rational product-class equivalence. It does not name an undefined Selmer group or manufacture a Sha theorem from a receipt. Its compilation and axiom audit pass, and the module is part of the default library. Further formal work must connect the coordinate ring to the actual cubic field and maximal order, prove the ideal/class-group and Dirichlet steps, instantiate the local Kummer valuation and square-lifting lemmas, and construct the finite Kummer exact sequence and Mordell–Weil rank bridge. These are formalization obligations for the conventional proof given above, rather than missing numerical evidence.

The old generator still refuses unsupported arithmetic certification. This change does not extend its accepted scope or alter historical receipts. PerfectPower's two-isogeny family is not imported: 389a1 has no rational nonidentity two-torsion, so that family's hypotheses fail. Its generic exact-sequence counting is conceptually compatible, but no dependency or formal integration is claimed.

Analytic rank, rigorous BSD enclosures, full Mordell–Weil saturation and the odd-primary part of Sha remain separate obligations for this focused proposal. No conclusion about full Sha triviality follows from the 2-primary result.

## Sources and provenance

The field and basic conventional descent argument were recovered from the previously saved `Selmer_389a1_Arithmetic_Proof_2026-11-04.zip`. This proposal freshly audits those arithmetic inputs and adds a standard-library certificate, explicit unit normalizations, dyadic and 389-adic square witnesses, mutation tests and precise rational-square Lean predicates. It does not present the recovered argument as a new discovery.

- Michael Stoll, [Descent on elliptic curves](https://www.mathe2.uni-bayreuth.de/stoll/schrift.html), course notes and published survey: the full cubic-algebra descent framework.
- Schaefer–Stoll, [How to do a p-descent on an elliptic curve](https://mathe2.uni-bayreuth.de/stoll/papers/p-descent-long.pdf): introductory discussion of full 2-descent and the finite Kummer exact sequence. The main body treats odd p; it is not substituted for a two-isogeny argument here.
- [MichaelStollBayreuth/EllipticCurves](https://github.com/MichaelStollBayreuth/EllipticCurves): a possible formalization route for full descent and local images. Its advertised general results were inspected, but the external library was not replayed, imported, or independently axiom-audited here.
- [Trust repair PR #1](https://github.com/towre676-cloud/certified-selmer-pipeline/pull/1), still open when inspected; [PerfectPower PR #15](https://github.com/towre676-cloud/perfectpower/pull/15), merged, with different curve-family hypotheses.
