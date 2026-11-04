# 389a1: a checked arithmetic proof and rigorous numerical enclosures

November 4, 2026. Curve: `E : y²+y=x³+x²−2x`, with minimal discriminant 389. This is a follow-up to certified-selmer-pipeline PR #1, head `87037a1fd06945d3cc5fe9c821758ccd43095eff`.

**Status.** The argument below proves the arithmetic conclusions using standard theorems of explicit 2-descent, algebraic number theory, canonical heights and modularity. All the curve-specific finite calculations and numerical bounds are supplied by executable checks. A fresh PARI full descent independently agrees. This is not an end-to-end Lean formalization: Lean replays 19 explicitly limited statements, including ten new finite arithmetic facts, with empty axiom lists. The cohomological, number-field, height and analytic identifications in this proof remain outside that kernel replay. No unproved arithmetic assertion is introduced into Lean as an axiom.

The results established by this argument are

\[
E(\mathbb Q)=\mathbb Z(0,0)\oplus\mathbb Z(1,0),\qquad
\operatorname{Sel}_2(E/\mathbb Q)\cong(\mathbb Z/2)^2,
\qquad \Sha(E/\mathbb Q)[2^\infty]=0.
\]

The analytic rank is also two, and rigorous enclosures validate the old receipt's regulator and leading-coefficient intervals. **Triviality of the whole of Sha is not established.** The original generic proof generator still refuses arithmetic certification, because these paper-level identifications are not yet implemented as a formal certificate backend.

## 1. A small descent field, with class number one

Complete the square and scale by setting `X=4x`, `Y=8y+4`. The curve becomes

\[
Y^2=F(X),\qquad F(X)=X^3+4X^2-32X+16.
\]

Let

\[
g(T)=T^3-T^2-9T+11,\quad K=\mathbb Q(\beta),\quad g(\beta)=0.
\]

The exact polynomial identity `F(2T−2)=8g(T)` identifies the root of F as `θ=2β−2`. The polynomial `g(T+1)=T³+2T²−8T+2` is Eisenstein at 2, so g is irreducible and 2 is totally ramified in K, with one prime and residue degree one. Its polynomial discriminant is `1556=4·389`.

The order `Z[β]` is maximal. No odd prime can divide its index: the only possible odd prime is 389 and its discriminant valuation is one. At 2 the local degree-three extension is totally ramified and tame, hence its discriminant exponent is `3−1=2`, equal to the exponent in the polynomial discriminant. The index at 2 is also one. Thus the field discriminant is 1556.

The three sign-changing rational brackets

\[
(-3.081,-3.080),\quad(1.270,1.271),\quad(2.809,2.810)
\]

exhaust the roots, so K is totally real. The Minkowski bound for an ideal class is `(2/9)√1556<9`; after squaring this is the integer comparison `6224<6561`.

The only prime ideals with norm below nine can lie over 2, 3, 5 or 7. At 2 there is just the degree-one prime, principal because

\[
N_{K/\mathbb Q}(\beta-3)=-g(3)=-2.
\]

Modulo 3 the factorization is

\[
g(T)=(T+1)(T^2+T+2),
\]

and the quadratic is irreducible. The unique norm-three prime is principal because `N(β−2)=−g(2)=3`; its residue root is β=2. The other prime above 3 has norm nine and lies outside the strict Minkowski bound. The cubic has no root modulo either 5 or 7 and is irreducible at both, so their prime ideals have norms 125 and 343. Therefore every prime ideal that can generate an ideal class is principal. **The class group is trivial.** This argument does not assume GRH, a regulator approximation or a supplied class-number assertion. Independently, `bnfinit` followed by `bnfcertify` returns certified class number one.

## 2. A Selmer upper bound of four

The standard full 2-descent embeds the 2-Selmer group into the norm kernel of `K×/K×²`. The Kummer image of a point on the scaled model is `[X−θ]`. We show that any Selmer class has even ideal valuation at every finite prime of K.

At an odd rational prime not dividing the discriminant of F, the polynomial is étale. For a local point with integral X, only one degree-one prime can divide `X−θ`, and the square norm `N(X−θ)=Y²` forces its valuation to be even. If X is nonintegral, the elliptic-curve equation forces its valuation to be a negative even integer; at every prime above p the valuation of `X−θ` is that even integer multiplied by the ramification index.

The remaining odd prime is 389. Here `v₃₈₉(disc F)=1` and the exact reduction is

\[
F(X)=(X+62)(X-29)^2\pmod {389}.
\]

The local algebra is a simple linear factor and a ramified quadratic factor. Explicitly `F(29)=389·69` and `F′(29)=389·7`, giving the uniformizer valuation in the ramified factor. If an integral X reduces to the double root 29, its difference from a root of the ramified quadratic has valuation one at that ramified prime: the root differs from a lift of 29 by a uniformizer, while the rational X differs by a multiple of 389. Its norm would then have odd valuation, contradicting `Y²`. If X reduces to the simple root, only the unramified degree-one factor contributes, and its valuation is even by the norm condition. Otherwise all factors are units. The same conclusion applies to local order-two points via the usual continuous extension of the Kummer map; equivalently they can be approximated by non-order-two local points with the same square class. This is the standard discriminant-exponent-at-most-one refinement of the valuation lemma in full 2-descent.

Thus the only possible odd valuations are over 2. There is exactly one prime over 2, with residue degree one. The square norm forces its valuation to be even as well.

For a global class α, its fractional ideal is consequently an ideal square. Class number one allows division by the square of a principal generator, giving a representative in `O_K×`. Dirichlet's theorem says that the totally real cubic unit group has free rank two and torsion `{±1}`. Its unit square-class group has order eight. The norm of −1 is −1, a nonsquare in Q, so the norm kernel on these eight classes has order four. We have proved

\[
\#\operatorname{Sel}_2(E/\mathbb Q)\le4.
\]

This is an upper bound: it requires no unsupported assertion that arbitrary locally soluble covers are globally soluble.

## 3. Two actual independent Kummer classes

Let `P=(0,0)` and `Q=(1,0)`. Direct substitution checks both curve equations. Their scaled Kummer representatives are

\[
\alpha_P=2-2\beta,\qquad\alpha_Q=6-2\beta.
\]

At the three real embeddings, αP has signs `(+,-,-)` while αQ is positive at all three, since the largest root of g is less than 3. A square cannot be negative in a real embedding. This rules out both αP and αPαQ as squares.

At the norm-three prime, β reduces to 2 and αQ reduces to `6−4=2`. It is a unit with nonsquare residue in F3, so αQ cannot be a square either. The classes `[1], [αP], [αQ], [αPαQ]` are four distinct actual Kummer classes. Hence

\[
4\le\# E(\mathbb Q)/2E(\mathbb Q)\le\#\operatorname{Sel}_2(E/\mathbb Q)\le4.
\]

There is no nonidentity rational two-torsion: F is irreducible. Mordell–Weil finite generation now gives **rank exactly two**, and the finite Kummer exact sequence gives `Sha[2]=0`. Repeated doubling of a nonzero element of finite 2-power order would produce a nonzero element of order two. Therefore **Sha[2∞]=0**, with no assumption that all of Sha is finite.

The infinite Kummer sequence then gives

\[
\operatorname{Sel}_{2^\infty}(E/\mathbb Q)\cong(\mathbb Q_2/\mathbb Z_2)^2.
\]

It is nonzero. Thus “full infinite-Selmer vanishing” is not a correct theorem for this curve.

## 4. Full Mordell–Weil basis: an explicit saturation argument

Independent point counting gives `#E(F5)=9` and `#E(F7)=13`. Good reduction makes rational torsion inject at these primes; the coprime counts prove that the torsion subgroup is trivial.

To prove that P and Q form a full basis, rather than an odd-index subgroup, use canonical heights. We use the normalization

\[
H(R)=\lim_{n\to\infty}4^{-n}h(x(2^nR)),
\quad B(R,S)=\tfrac12(H(R+S)-H(R)-H(S)),
\]

which agrees with the PARI/Cremona height-matrix convention used by the original receipt. All nonzero rational points have positive H.

Shift the coordinate to `u=x+4`. Then

\[
y^2+y=u^3-11u^2+38u-40,
\qquad(b_2,b_4,b_6,b_8)=(-44,76,-159,305).
\]

All real points have `u>19/10`. For `t=1/u` define

\[
z(t)=1-76t^2+318t^3-305t^4,
\quad w(t)=4t-44t^2+152t^3-159t^4,
\quad t_{n+1}=w(t_n)/z(t_n).
\]

The real locus lies in the two t-intervals `[0,0.204]` and `[0.241,0.511]`. Exact rational Bernstein coefficients on 200 subdivisions of each interval prove

\[
1/1024<z(t)<1024.
\]

The minimum Bernstein lower bound produced by the checker is `0.008167896895`, safely larger than `1/1024`. The upper bound follows already from the sum of absolute coefficients for `0≤t≤1`. Thus Tate's archimedean series has a uniform, explicit tail bound.

Write a rational point as `x=A/D²`, with `D>0` and `gcd(A,D)=1`, and put `B=A+4D²>0`. At the sole bad prime, the minimal discriminant has valuation one and Tamagawa number one. The nonarchimedean local height terms are therefore the denominator contribution plus the discriminant normalization, which cancels the archimedean discriminant term. The local-height formula yields

\[
H(R)=\log B+\sum_{n=0}^{\infty}4^{-n-1}\log z(t_n).
\]

For integral x, `B=u`; these are the points used for the displayed height matrix. The tail after m terms has absolute value at most `10 log(2)/(3·4^m)`. At `m=60`, ball arithmetic gives every listed height with this analytic tail included.

For any point with `H(R)≤1/4`, the uniform lower series bound gives

\[
B\le \exp(1/4)\,2^{10/3}<13.
\]

Also `u=B/D²>19/10`, so `D²<120/19<7` and `D≤2`. Exhausting the finitely many reduced fractions with `1≤B≤12` and `D=1,2` gives precisely the x-coordinates

\[
-2,-1,0,1,3,4,6,
\]

with their two corresponding y-values. Every one has a rigorous height enclosure strictly greater than `1/4`; the smallest is `H(P)=0.32700077365160…`. Consequently every nonzero rational point has `H(R)>1/4`.

Since `P+Q=(-2,-1)`, the same calculation gives the pairing and determinant

\[
D_{P,Q}=H(P)H(Q)-B(P,Q)^2
=0.15246017794314375162432475704945582\ldots<3/16.
\]

If their subgroup had index `m≥2`, the planar Hermite bound applied to the full Mordell–Weil lattice would give a nonzero R with

\[
H(R)^2\le\frac4{3}\frac{D_{P,Q}}{m^2}
\le\frac{D_{P,Q}}3<\frac1{16},
\]

contradicting `H(R)>1/4`. Thus m=1: **P and Q are a full basis**, and the determinant is the full regulator in the stated normalization. No finite list of saturation primes or unverified point-database basis claim is being substituted for this argument.

## 5. Rigorous numerical enclosures and analytic rank

The checker uses python-flint/Arb at 1024-bit working precision. All receipt endpoints are stored as exact rational numbers, with display strings for readability. The results include

| Quantity | Rigorous displayed enclosure |
|---|---|
| Full regulator | `0.15246017794314375162432475704945582 ± 5.48e−36` |
| Total real period | `4.9804251217101101506427155838846049203 ± 1.22e−38` |
| `L''(E,1)/2` | `0.759316500288426770230192607895 ± 5.38e−31` |

These intervals lie strictly within the original receipt's regulator and leading-coefficient intervals. Their validity comes from this fresh derivation, not from a hash or comparison of approximate samples.

For the period, isolate all three roots βi by exact rational bisection and put `ei=(βi−1)/2`. There are two real components. The total Néron real period is

\[
\Omega=\frac{2\pi}{\operatorname{AGM}(\sqrt{e_3-e_1},\sqrt{e_3-e_2})},
\]

with β1<β2<β3. The root intervals and AGM are rigorously enclosed.

For the L-value, Δ=389 gives a minimal semistable curve with conductor 389 and split nodal reduction at 389. The tangent coefficient at the node is a square modulo 389, checked explicitly. The global root number is +1. Modularity supplies the weight-two form `f`, with Fourier coefficients computed directly from exhaustive finite-field point counts, multiplicativity and the Euler recurrences. All coefficients through 256 are independently compared with PARI's `ellan`.

Exact vanishing of `L(E,1)` follows from rank two and the proved rank-zero direction of the Gross–Zagier–Kolyvagin theory: for a modular elliptic curve, `L(E,1)≠0` would force rank zero. This is use of a proved theorem, not BSD. Independently, PARI's rational modular-symbol evaluation of the path from 0 to infinity is exactly zero. The functional equation with sign +1 then forces the first derivative to vanish as well.

Let `c=2π/√389` and `F₀(t)=Σ a_n exp(−cnt)`. Splitting the Mellin integral at t=1 and using those exact lower-order vanishings gives

\[
\frac{L''(E,1)}2=c\int_1^\infty F_0(t)(\log t)^2\,dt.
\]

The finite integral uses the first M=256 coefficients on `[1,T]`, T=256, with Arb's validated complex quadrature and its analytic branch flag for log. The coefficient bound `|a_n|≤n²` follows from the Hasse/Euler bounds and `d(n)≤2√n` (n=1 handled separately). Using `(log t)²≤t²`, the omitted Fourier tail is at most

\[
q^{M+1}\left(\frac{M+1}{1-q}+\frac q{(1-q)^2}
+\frac{2/c+2/c^2}{1-q}\right),\quad q=e^{-c}.
\]

The t-tail, bounding all coefficients, is at most

\[
e^{-cT}(T^2+2T/c+2/c^2)\frac{1+e^{-cT}}{(1-e^{-cT})^3}.
\]

They are respectively below `2.91e−33` and `2.57e−31`, and both are added to the quadrature radius. A second run with different truncation and height parameters checks overlap with the resulting enclosures. The positive second derivative and exact first two vanishings prove **analytic rank exactly two**.

The numerical BSD quotient is enclosed extremely near one. We do not infer that it equals an integer, that the full BSD formula holds, or that all of Sha is trivial.

## 6. Formal boundary and reproducibility

The ten new kernel-replayed Lean statements concern the displayed discriminant, norm witnesses, Minkowski integer comparison, finite residue obstructions and finite-field point counts. Together with the original nine limited facts there are **19 declarations, all axiom-free**. The existing generator does not turn the paper's conclusions into alleged Lean arithmetic theorems. Full formalization still requires the actual cubic number field, ideal valuations and class-group proof, the Kummer/Selmer exactness bridge, the height/saturation argument and analytic identifications.

A relevant formalization route is Michael Stoll's [EllipticCurves project](https://github.com/MichaelStollBayreuth/EllipticCurves), inspected at `bad38e242a187dea006fc302a0ef0fd53eedd4ba`. Its general descent machinery is a more suitable direction for 389a1 than PerfectPower's rational two-isogeny family. No compatibility, complete axiom audit, or replay of that external library is claimed here, and it uses a newer Lean toolchain than this small project.

Reproduce locally:

```bash
python3 -m pip install -r arithmetic/requirements.txt
python3 arithmetic/verify_389.py
python3 arithmetic/pari_replay.py
python3 -m unittest discover -s tests -v
python3 python/audit_lean.py
```

The CAS replay uses bundled PARI 2.15.4, through cypari 2.5.7. The independent checker uses exact integer/rational operations, Sympy polynomial arithmetic and python-flint 0.9.0. PARI is not used to produce its regulator, period, Fourier coefficients or L-value enclosure. Its trust boundary is the correctness of those libraries plus the standard mathematical lemmas identified above. This is substantially stronger arithmetic evidence than the original receipts, while remaining distinct from full formal proof.

## 7. What remains open in this work

The full Sha group has not been proved trivial, nor has its finiteness been proved by this work. The 2-primary result does not control any odd-primary subgroup. A general odd-primary theorem must have its hypotheses verified for this curve, or independently checkable p-descent arguments must cover every possible prime; checking a few small primes is insufficient. A numerical BSD quotient near one supplies none of these missing logical steps.

The follow-up source and proof are prepared for review. No additional GitHub commit or merge was performed during this arithmetic pass. The first PR's two GitHub runs have succeeded; these new arithmetic changes have only been tested locally.

## Primary references and mathematical dependencies

- Standard explicit full 2-descent and the Kummer exact sequence, as described by Schaefer–Stoll, *How to do a p-descent on an elliptic curve*, Trans. AMS 356 (2004), 1209–1231, [DOI](https://doi.org/10.1090/S0002-9947-03-03366-X).
- Tate local-height series and normalization: J. H. Silverman, *Computing heights on elliptic curves*, Math. Comp. 51 (1988), 339–358, [DOI](https://doi.org/10.1090/S0025-5718-1988-0942161-4). The uniform z-bound and tail constants here are proved explicitly above.
- [PARI elliptic-curve documentation](https://pari.math.u-bordeaux.fr/dochtml/html-stable/Elliptic_curves.html) defines unconditional rank bounds, the cover-basis output and the distinction from numerical BSD evidence; [modular-symbol documentation](https://pari.math.u-bordeaux.fr/dochtml/html-stable/Modular_symbols.html) specifies the exact rational-symbol construction.
- [Arb integration documentation](https://python-flint.readthedocs.io/en/latest/acb.html) specifies validated quadrature and the required analytic flag for branch functions; [Arb real arithmetic](https://python-flint.readthedocs.io/en/latest/arb.html) specifies outward enclosures.
- The rank-zero implication used for the exact analytic vanishing is the standard completed Kolyvagin theorem for modular elliptic curves; its original development includes [Kolyvagin's finiteness paper](https://www.mathnet.ru/eng/im1191). We do not apply its rank-at-most-one Sha finiteness conclusion to this rank-two curve.
