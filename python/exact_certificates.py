"""Small exact checkers; none establish Selmer completeness or numerical enclosures."""
from itertools import permutations
from verify_receipts import require

def determinant(a):
    n = len(a)
    total = 0
    for p in permutations(range(n)):
        inversions = sum(p[i] > p[j] for i in range(n) for j in range(i+1, n))
        term = (-1)**inversions
        for i in range(n):
            term *= a[i][p[i]]
        total += term
    return total

def multiply(a, b):
    return [[sum(x*y for x, y in zip(row, col)) for col in zip(*b)] for row in a]

def verify_smith(a, u, v, diagonal):
    # Deliberately bounded independent checker, with factorial determinant cost.
    n = len(diagonal)
    require(1 <= n <= 6, 'Smith checker supports square dimensions 1..6')
    for m in (a, u, v):
        require(isinstance(m, list) and len(m) == n and
                all(isinstance(r, list) and len(r) == n and
                    all(type(x) is int for x in r) for r in m), 'bad integer matrix')
    require(all(type(x) is int and x > 0 for x in diagonal), 'bad diagonal')
    require(all(y % x == 0 for x, y in zip(diagonal, diagonal[1:])), 'not Smith divisibility')
    require(abs(determinant(u)) == abs(determinant(v)) == 1, 'non-unimodular witnesses')
    target = [[diagonal[i] if i == j else 0 for j in range(n)] for i in range(n)]
    require(multiply(multiply(u, a), v) == target, 'U A V != diagonal')
    return True

def curve_facts():
    # Model from Cremona's table. It is external to the original legacy receipt.
    a1, a2, a3, a4, a6 = 0, 1, 1, -2, 0
    b2 = a1*a1 + 4*a2
    b4 = a1*a3 + 2*a4
    b6 = a3*a3 + 4*a6
    b8 = a1*a1*a6 + 4*a2*a6 - a1*a3*a4 + a2*a3*a3 - a4*a4
    disc = -b2*b2*b8 - 8*b4**3 - 27*b6*b6 + 9*b2*b4*b6
    require(disc == 389, 'bad discriminant')
    require(all(y*y+y == x**3+x*x-2*x for x,y in [(0,0),(1,0)]), 'bad points')
    # Rational order-two points satisfy y=-1/2 and 4x^3+4x^2-8x+1=0.
    # t=4x then satisfies MONIC t^3+4t^2-32t+16=0.
    # Rational root theorem: rational t must be an integer dividing 16.
    candidates = [s*d for d in (1,2,4,8,16) for s in (-1,1)]
    values = [t**3+4*t*t-32*t+16 for t in candidates]
    require(all(values), 'rational two-torsion root found')
    residues = [(t**3+4*t*t-32*t+16) % 5 for t in range(5)]
    require(all(residues), 'mod-five obstruction failed')
    return dict(ainvs=[a1,a2,a3,a4,a6], discriminant=disc,
                rational_root_candidates=candidates, polynomial_values=values,
                mod_five_residues=residues, rational_two_torsion_order=1,
                rank_certified=False, selmer_certified=False)

if __name__ == '__main__':
    import json
    print(json.dumps(curve_facts(), indent=2))
