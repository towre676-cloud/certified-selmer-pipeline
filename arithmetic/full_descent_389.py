"""Portable exact finite-input checker for full 2-descent on 389a1.
Python standard library only. The conventional arithmetic proof is in
../docs/FULL_2_DESCENT_389.md. This does not implement Galois cohomology,
ideal theory, or a Lean proof of that theorem. Run with python -O too:
no security or mathematical validation depends on assert statements.
"""
from fractions import Fraction as Q
from itertools import permutations, product
from math import gcd, isqrt
from pathlib import Path
import argparse
import json

class InvalidCertificate(ValueError): pass

def require(ok, message):
    if not ok: raise InvalidCertificate(message)

def ints(xs, n):
    require(type(xs) is list and len(xs)==n and all(type(x) is int for x in xs), 'integer vector schema')
    return tuple(xs)

def add(a,b): return tuple(x+y for x,y in zip(a,b))
def scale(k,a): return tuple(k*x for x in a)

def mul(a,b):
    """Multiplication in Z[b]/(b^3-b^2-9b+11), ascending coordinates."""
    c=[0]*5
    for i in range(3):
        for j in range(3):c[i+j]+=a[i]*b[j]
    for i in (4,3):
        c[i-3]-=11*c[i];c[i-2]+=9*c[i];c[i-1]+=c[i]
    return tuple(c[:3])

def power(a,n):
    ans=(1,0,0)
    for _ in range(n):ans=mul(ans,a)
    return ans

def det(m):
    require(len(m)==len(m[0]) and all(len(r)==len(m) for r in m),'square matrix')
    n=len(m);v=0
    for p in permutations(range(n)):
        term=(-1)**sum(p[i]>p[j] for i in range(n) for j in range(i+1,n))
        for i in range(n):term*=m[i][p[i]]
        v+=term
    return v

def norm(a):
    columns=[mul(a,e) for e in [(1,0,0),(0,1,0),(0,0,1)]]
    return det(list(zip(*columns)))

def trace(a):
    return sum(mul(a,e)[i] for i,e in enumerate([(1,0,0),(0,1,0),(0,0,1)]))

def evalpoly(a,x):
    y=0
    for c in reversed(a):y=y*x+c
    return y

def polymul(a,b):
    c=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):c[i+j]+=x*y
    return c

def compose_linear(a,u,v):
    out=[0]*len(a);term=[1]
    for c in a:
        for j,z in enumerate(term):out[j]+=c*z
        term=polymul(term,[v,u])
    return out

def discr(a):
    d,c,b,aa=a
    require(aa==1,'monic cubic')
    return b*b*c*c-4*c**3-4*b**3*d-27*d*d+18*b*c*d

def isprime(p):return type(p) is int and p>=2 and all(p%d for d in range(2,isqrt(p)+1))

def count(p):
    return 1+sum((y*y+y-x*x*x-x*x+2*x)%p==0 for x in range(p) for y in range(p))

def no_duplicates(pairs):
    d={}
    for k,v in pairs:
        require(k not in d,'duplicate JSON key');d[k]=v
    return d

def load(path):
    return json.loads(Path(path).read_text(),object_pairs_hook=no_duplicates,
                      parse_constant=lambda _: (_ for _ in ()).throw(InvalidCertificate('nonfinite JSON')))

def verify(c):
    require(type(c) is dict and set(c)=={'schema','ainvs','g','F','brackets','prime_generators','units','covers','odd_bad_factor','bad_root','minkowski_square','local_witnesses'},'top-level schema')
    require(c['schema']=='389a1-full-2-descent-v1','schema version')
    require(ints(c['ainvs'],5)==(0,1,1,-2,0),'curve binding')
    g=ints(c['g'],4);f=ints(c['F'],4)
    require(g==(11,-9,-1,1) and f==(16,-32,4,1),'field binding')
    require(compose_linear(f,2,-2)==[8*x for x in g],'F(2b-2)=8g(b)')
    require(compose_linear(g,1,1)==[2,-8,2,1],'Eisenstein shift')
    require(discr(g)==1556 and discr(f)==99584,'cubic discriminants')
    require(isprime(389) and 1556==4*389 and 99584==64*1556,'discriminant support')
    # beta basis trace pairing supplies an independent discriminant computation.
    basis=[(1,0,0),(0,1,0),(0,0,1)]
    gram=[[trace(mul(a,b)) for b in basis] for a in basis]
    require(det(gram)==1556,'trace pairing discriminant')
    require(type(c['brackets']) is list and len(c['brackets'])==3,'root bracket schema')
    brackets=[]
    for pair in c['brackets']:
        require(type(pair) is list and len(pair)==2 and all(type(t) is str for t in pair),'rational brackets')
        a,b=map(Q,pair)
        require(a<b and evalpoly(g,a)*evalpoly(g,b)<0,'root sign change')
        brackets.append((a,b))
    require(brackets[0][1]<brackets[1][0] and brackets[1][1]<brackets[2][0],'disjoint root brackets')
    require(brackets[0][1]<1<brackets[1][0] and brackets[2][1]<3,'Kummer signs')
    require(ints(c['minkowski_square'],2)==(6224,6561) and 4*1556<81**2,'Minkowski <9')
    require(type(c['prime_generators']) is dict and set(c['prime_generators'])=={'2','3'},'principal witnesses')
    pi=ints(c['prime_generators']['2'],3);rho=ints(c['prime_generators']['3'],3)
    require(pi==(-3,1,0) and rho==(-2,1,0) and norm(pi)==-2 and norm(rho)==3,'principal prime norms')
    require(all((a-b)%3==0 for a,b in zip(g,polymul([1,1],[2,1,1]))),'factorization at 3')
    require(all((r*r+r+2)%3 for r in range(3)),'irreducible quadratic at 3')
    require(all(evalpoly(g,r)%p for p in (5,7) for r in range(p)),'inert 5 and 7')
    bf=ints(c['odd_bad_factor'],4)
    require(bf==tuple(polymul([62,1],polymul([-29,1],[-29,1]))) and all((a-b)%389==0 for a,b in zip(f,bf)),'factorization at 389')
    r=c['bad_root'];require(type(r) is int and r==29,'bad root')
    value=evalpoly(f,r);deriv=3*r*r+8*r-32
    require(value==389*69 and deriv==389*7 and 69%389!=0,'ramified uniformizer witness')
    require((r+62)%389!=0,'simple and double roots distinct')
    require(type(c['covers']) is list and len(c['covers'])==3,'cover schema')
    deltas=[];cover_points=[]
    for row in c['covers']:
        require(type(row) is dict and set(row)=={'point','delta','z'},'cover row schema')
        x,y=ints(row['point'],2);delta=ints(row['delta'],3);z=ints(row['z'],3)
        require(y*y+y==x*x*x+x*x-2*x,'point on original curve')
        X,Y=4*x,8*y+4
        require(Y*Y==evalpoly(f,X),'scaled point')
        require(mul(delta,power(z,2))==(X+2,-2,0),'norm cover delta*z^2=X-theta')
        require(norm(delta)>0 and isqrt(norm(delta))**2==norm(delta),'square norm')
        deltas.append(delta);cover_points.append((x,y))
    require(cover_points==[(0,0),(1,0),(-2,-1)],'P,Q,P+Q witnesses')
    require(mul(mul(deltas[0],deltas[1]),deltas[2])==(16,0,0),'chord square relation')
    require(type(c['units']) is list and len(c['units'])==3,'unit schema')
    units=[ints(u,3) for u in c['units']]
    for d,u in zip(deltas,units):
        require(norm(u)==1 and mul(power(pi,4),u)==d,'explicit unit normalization')
    # Real obstruction for P and PQ; Q obstruction at degree-one prime over 3.
    require(deltas[0]==(2,-2,0) and deltas[1]==(6,-2,0),'independence representatives')
    require(evalpoly(deltas[1],2)%3==2 and all(r*r%3!=2 for r in range(3)),'Q nonsquare residue')
    require(evalpoly(g,2)%3==0 and (3*2*2-2*2-9)%3!=0,'simple prime over 3')
    local=c['local_witnesses']
    require(type(local) is dict and set(local)=={'two_product_square_mod8','389_Q_roots'},'local schema')
    z=ints(local['two_product_square_mod8'],3);ab=mul(units[0],units[1])
    require(norm(z)%2==1 and all((v-w)%8==0 for v,w in zip(mul(z,z),ab)),'2-adic PQ square lift')
    # In any extension of Q2, 1+8O consists of squares by Hensel.
    # Integral square roots of integral units lie in O (maximality proved in prose).
    residues={tuple(v%8 for v in mul(z,z)) for z in product(range(8),repeat=3)}
    require(tuple(v%8 for v in units[0]) not in residues,'2-adic P nonsquare')
    rr=ints(local['389_Q_roots'],2)
    for r,z in zip((-30,210),rr):
        require((2*r-2+62)%389==0 or (2*r-2-29)%389==0,'389 residue root')
        require(z%389!=0 and (z*z-evalpoly(units[1],r))%389==0,'389 Q square lifts')
    v=evalpoly(units[0],210)%389
    require(v!=0 and pow(v,194,389)==388,'389 P nonsquare in ramified factor')
    counts=[count(p) for p in (5,7)]
    require(counts==[9,13] and gcd(*counts)==1,'torsion counts')
    return {'status':'exact_finite_witnesses_passed','field_discriminant':1556,
            'trace_pairing':gram,'minkowski_bound_strictly_less_than':9,
            'principal_small_prime_norms':[-2,3],
            'finite_valuation_support_after_local_lemma':[],
            'unit_norm_kernel_dimension_by_Dirichlet':2,
            'independence_obstructions':['real sign of P and PQ','Q residue 2 at (3,beta-2)'],
            'local_image_basis_points':[[0,0],[1,0]],
            'finite_field_counts':dict(zip(['5','7'],counts)),
            'local_images_on_P_Q':{'real':[1,0],'2':[1,1],'389':[1,0]},
            'square_residues_mod8_enumerated':512,
            'formal_arithmetic_certified':False,
            'theory_boundary':'docs/FULL_2_DESCENT_389.md',
            'analytic_or_numerical_certification_performed':False}

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('certificate',nargs='?',default=str(Path(__file__).with_name('full_descent_389.json')))
    p.add_argument('--output');a=p.parse_args();report=verify(load(a.certificate))
    raw=json.dumps(report,indent=2)+'\n'
    if a.output:Path(a.output).write_text(raw)
    print(raw,end='')

if __name__=='__main__':main()
