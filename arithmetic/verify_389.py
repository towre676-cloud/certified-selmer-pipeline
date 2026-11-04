"""Independent finite arithmetic checks and rigorous Arb enclosures for 389a1.
The number-theoretic identifications are proved in CURVE389_PROOF.md, not in Lean.
No computation in this file proves full Sha triviality or BSD.
"""
from fractions import Fraction as Q
from math import comb, gcd, isqrt
from pathlib import Path
import argparse
import hashlib
import json
from flint import arb, acb, ctx, fmpq
import sympy as sp

HERE = Path(__file__).resolve().parent

def require(ok, message):
    if not ok: raise ValueError(message)

def g(x): return x**3-x**2-9*x+11

def F(x): return x**3+4*x**2-32*x+16

def interval(a,b):
    a,b=Q(a),Q(b)
    require(a <= b, 'reversed interval')
    mid=(a+b)/2;rad=(b-a)/2
    return arb(fmpq(mid.numerator,mid.denominator),fmpq(rad.numerator,rad.denominator))

def encode(v, digits=38):
    require(v.is_finite(),'nonfinite enclosure')
    return {'lo':str(v.lower().fmpq()),'hi':str(v.upper().fmpq()),'display':v.str(digits)}

def bernstein(coeffs,a,b):
    n=len(coeffs)-1
    cs=[sum(Q(coeffs[i])*comb(i,j)*a**(i-j)*(b-a)**j for i in range(j,n+1)) for j in range(n+1)]
    return [sum(cs[j]*Q(comb(k,j),comb(n,j)) for j in range(k+1)) for k in range(n+1)]

def finite_count(p):
    return 1+sum((y*y+y-x**3-x*x+2*x)%p == 0 for x in range(p) for y in range(p))

def root_intervals(bits=180):
    # Three disjoint sign-changing intervals exhaust the roots of a cubic.
    result=[]
    for l,r in [(Q(-3081,1000),Q(-3080,1000)),(Q(1270,1000),Q(1271,1000)),(Q(2809,1000),Q(2810,1000))]:
        require(g(l)*g(r)<0,'bad root bracket')
        for _ in range(bits):
            m=(l+r)/2
            if g(l)*g(m)<0:r=m
            else:l=m
        result.append((l,r))
    return result

def exact_checks():
    x=sp.Symbol('x')
    p=x**3-x**2-9*x+11
    f=x**3+4*x**2-32*x+16
    require(sp.expand(f.subs(x,2*x-2)-8*p)==0,'field coordinate identity')
    require(sp.discriminant(p,x)==1556 and sp.discriminant(f,x)==99584,'discriminants')
    require(sp.expand(p.subs(x,x+1))==x**3+2*x**2-8*x+2,'Eisenstein shift')
    require(4*1556 < 81*81,'Minkowski bound <9')
    for prime in [5,7]:require(all(g(r)%prime for r in range(prime)),'inert prime check')
    require(all(int(c)%3==0 for c in sp.Poly(p-(x+1)*(x*x+x+2),x).all_coeffs()),'factorization at 3')
    require(all((r*r+r+2)%3 for r in range(3)),'quadratic factor at 3')
    require(-g(3)==-2 and -g(2)==3,'principal prime norm witnesses')
    require(all(int(c)%389==0 for c in sp.Poly(f-(x+62)*(x-29)**2,x).all_coeffs()),'factorization at 389')
    require(F(29)==389*69 and 3*29**2+8*29-32==389*7,'ramified-root uniformizer data')
    require((6-2*2)%3==2 and all(r*r%3!=2 for r in range(3)),'Kummer residue obstruction')
    counts={p:finite_count(p) for p in [5,7]}
    require(counts=={5:9,7:13} and gcd(*counts.values())==1,'torsion reduction counts')
    node_x=(29*pow(4,-1,389))%389
    tangent=(3*node_x+1)%389
    square_root=next((t for t in range(389) if t*t%389==tangent),None)
    require(square_root is not None,'split nodal reduction')
    # Global z-bound, verified by exact rational Bernstein coefficients.
    minimum=Q(1)
    domains=[(Q(0),Q(204,1000)),(Q(241,1000),Q(511,1000))]
    for a,b in domains:
        for k in range(200):
            l=a+(b-a)*Q(k,200);r=a+(b-a)*Q(k+1,200)
            minimum=min(minimum,*bernstein([1,0,-76,318,-305],l,r))
    require(minimum>Q(1,1024),'global Tate z lower bound')
    require(1+76+318+305<1024,'global Tate z upper bound')
    roots=root_intervals()
    # Domain coverage for all real points, using outer rational root bounds.
    require(Q(2)/(roots[2][0]+7)<Q(204,1000),'unbounded component t-range')
    require(Q(241,1000)<Q(2)/(roots[1][1]+7),'bounded component t lower')
    require(Q(2)/(roots[0][0]+7)<Q(511,1000),'bounded component t upper')
    require((roots[0][0]+7)/2>Q(19,10),'u>19/10')
    small=[]
    for d in (1,2):
        for b in range(1,13):
            a=b-4*d*d
            if gcd(a,d)!=1:continue
            xx=Q(a,d*d);disc=1+4*(xx**3+xx*xx-2*xx)
            if disc<0:continue
            rn,rd=isqrt(disc.numerator),isqrt(disc.denominator)
            if rn*rn==disc.numerator and rd*rd==disc.denominator:
                yy=(-1+Q(rn,rd))/2
                small.append({'x':str(xx),'y':str(yy),'B':b,'D':d})
    require([p['x'] for p in small]==['-2','-1','0','1','3','4','6'],'small height enumeration')
    return {'cubic_coefficients':[11,-9,-1,1],'field_discriminant':1556,
            'norm_witnesses':{'beta_minus_3':-2,'beta_minus_2':3},
            'minkowski_bound_squared_comparison':[4*1556,81*81],
            'finite_reduction_counts':counts,'tate_z_bernstein_min':str(minimum),
            'root_intervals':[[str(a),str(b)] for a,b in roots],
            'small_height_candidates':small,'split_node_x':node_x,'split_tangent_square':tangent,
            'split_tangent_root':square_root}

def height(xx,steps=60):
    xx=Q(xx);u=arb(fmpq(xx.numerator,xx.denominator))+4
    t=1/u;value=u.log()
    for n in range(steps):
        z=1-76*t*t+318*t**3-305*t**4
        require(z>0,'Tate iteration lost positivity/precision')
        value+=z.log()/arb(4)**(n+1)
        w=4*t-44*t*t+152*t**3-159*t**4
        t=w/z
    tail=10*arb.const_log2()/(3*arb(4)**steps)
    return value+arb(0,tail)

def fourier_coefficients(M):
    aps={}
    for p in range(2,M+1):
        if all(p%d for d in range(2,isqrt(p)+1)):
            aps[p]=p+1-finite_count(p)
    ans=[0,1]
    for n in range(2,M+1):
        p=next(p for p in aps if n%p==0);m=n;e=0
        while m%p==0:e+=1;m//=p
        a0,a1=1,aps[p]
        for _ in range(2,e+1):a0,a1=a1,aps[p]*a1-(p if p!=389 else 0)*a0
        ans.append(ans[m]*a1)
    return ans

def leading_coefficient(ans,T=256):
    M=len(ans)-1;c=2*arb.pi()/arb(389).sqrt()
    def fun(t,analytic):
        q=(-acb(c)*t).exp();s=acb(0)
        for a in reversed(ans[1:]):s=(s+a)*q
        return c*s*t.log(analytic=analytic)**2
    finite=acb.integral(fun,1,T,abs_tol=arb(2)**-160,rel_tol=arb(2)**-160,
                        eval_limit=100000,depth_limit=100).real
    q=(-c).exp()
    tailn=q**(M+1)*((M+1)/(1-q)+q/(1-q)**2+(2/c+2/c**2)/(1-q))
    qt=(-c*T).exp()
    tailt=qt*(T*T+2*T/c+2/c**2)*(1+qt)/(1-qt)**3
    return finite+arb(0,tailn+tailt),tailn,tailt

def run(bits=1024,steps=60,M=256,T=256):
    ctx.prec=bits
    exact=exact_checks()
    roots=[interval(a,b) for a,b in exact['root_intervals']]
    aa=((roots[2]-roots[0])/2).sqrt();bb=((roots[2]-roots[1])/2).sqrt()
    period=2*arb.pi()/aa.agm(bb)
    heights={p['x']:height(p['x'],steps) for p in exact['small_height_candidates']}
    require(all(h>arb(1)/4 for h in heights.values()),'minimum-height finite checks')
    require((arb(1)/4+10*arb.const_log2()/3).exp()<13,'B<13 height cutoff')
    hp,hq,hr=(heights[str(x)] for x in [0,1,-2]);bil=(hr-hp-hq)/2
    reg=hp*hq-bil*bil
    require(0<reg<arb(3)/16,'positive determinant and saturation cutoff')
    ans=fourier_coefficients(M)
    lead,tailn,tailt=leading_coefficient(ans,T)
    require(lead>0,'positive second derivative coefficient')
    return {'status':'finite_arithmetic_and_ball_enclosures_checked',
            'formal_curve_theorem':False,'full_sha_triviality_proved':False,
            'theory_required':'See CURVE389_PROOF.md; Kummer descent, local valuation lemma, '
                'Minkowski, Dirichlet, MW, local heights, Hermite, modularity and L(1) vanishing theorem',
            'precision_bits':bits,'tate_steps':steps,'fourier_terms':M,'integration_cutoff':T,
            'exact':exact,'heights':{x:encode(v) for x,v in heights.items()},
            'height_pairing':encode(bil),'regulator':encode(reg),'real_period_total':encode(period),
            'L_second_derivative_over_2':encode(lead),'fourier_tail_bound':encode(tailn),
            'integration_tail_bound':encode(tailt),'BSD_quotient_numeric_only':encode(lead/(period*reg)),
            'fourier_coefficients':ans[1:]}

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output',default=str(HERE/'curve389_verified.json'))
    args=p.parse_args();result=run()
    result['source_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    Path(args.output).write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'status':result['status'], **{k:result[k]['display'] for k in ['regulator','real_period_total','L_second_derivative_over_2']}, 'full_sha_triviality_proved':False},indent=2))

if __name__=='__main__':main()
