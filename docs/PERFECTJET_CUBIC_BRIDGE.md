# PerfectJet cubic-field arithmetic bridge

The 389a1 pipeline now has an independent cross-repository replay of its
monogenic cubic arithmetic.

The maintained checker in `arithmetic/full_descent_389.py` works in

[
mathbf Z[eta]/(eta^3-eta^2-9eta+11)
]

with its own reduction, determinant, norm, and trace code. PerfectJet now
contains a generic dependency-free engine for the corresponding rational
quotient algebra. The bridge compares the two implementations without changing
the Selmer checker.

The replay includes:

- 125 exact elements with native/PerfectJet norm and trace comparison;
- 1,625 exact multiplication comparisons;
- the trace-pairing matrix
  [
  egin{pmatrix}
  3&1&19\
  1&19&-5\
  19&-5&155
  end{pmatrix};
  ]
- power-basis discriminant (1556);
- (N(eta-3)=-2) and (N(eta-2)=3);
- all retained cover identities
  [
  delta z^2=X-	heta,qquad 	heta=2eta-2;
  ]
- the three unit normalizations by ((eta-3)^4);
- the retained chord-square relation.

## Boundary

This bridge certifies arithmetic in the **presented quotient algebra**. It does
not prove that the quotient is the maximal order of the number field. In
particular, the Mathlib theorem identifying the field discriminant with 1556
depends on the separate maximal-order argument. Class number one, local
squareclasses, Selmer exactness, rank, and (Sha[2^infty]) remain separate
obligations.
