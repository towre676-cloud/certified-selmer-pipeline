from flint import arb, acb, ctx, fmpq, fmpz_poly
from fractions import Fraction as Q
from math import comb
ctx.prec=1024

def interval(a,b):
 a=Q(a);b=Q(b)
 return arb(fmpq((a+b).numerator,2*(a+b).denominator), fmpq((b-a).numerator,2*(b-a).denominator))

def bernstein(coeffs,a,b):
 # coeff of s^j in P(a+(b-a)s), then Bernstein coeff b_k=sum c_j C(k,j)/C(n,j).
 n=len(coeffs)-1
 cs=[sum(Q(coeffs[i])*comb(i,j)*a**(i-j)*(b-a)**j for i in range(j,n+1)) for j in range(n+1)]
 return [sum(cs[j]*Q(comb(k,j),comb(n,j)) for j in range(k+1)) for k in range(n+1)]

minimum=Q(1)
for a,b in [(Q(0),Q(204,1000)),(Q(241,1000),Q(511,1000))]:
 for k in range(200):
  l=a+(b-a)*Q(k,200);r=a+(b-a)*Q(k+1,200)
  minimum=min(minimum,*bernstein([1,0,-76,318,-305],l,r))
print('z Bernstein lower bound',float(minimum), minimum>Q(1,1024))

def height(x,steps=60):
 t=1/(arb(str(x))+4)
 value=(arb(str(x))+4).log()
 for n in range(steps):
  z=1-76*t*t+318*t**3-305*t**4
  value+=z.log()/arb(4)**(n+1)
  w=4*t-44*t*t+152*t**3-159*t**4
  t=w/z
 tail=10*arb.const_log2()/(3*arb(4)**steps)
 return value+arb(0,tail)
for x in [-2,-1,0,1,3,4,6]:print('H',x,height(x).str(40))
hp,hq,hr=map(height,[0,1,-2]);bil=(hr-hp-hq)/2
reg=hp*hq-bil*bil
print('reg',reg.str(40))
roots=sorted([r.real for r,m in fmpz_poly([11,-9,-1,1]).complex_roots()])
a=((roots[2]-roots[0])/2).sqrt();b=((roots[2]-roots[1])/2).sqrt()
period=2*arb.pi()/a.agm(b)
print('period',period.str(40))
# Independent exact coefficients by exhaustive finite-field point counts and Euler recurrence.
M=256;T=256
aps={}
for p in range(2,M+1):
 if all(p%d for d in range(2,int(p**.5)+1)):
  aps[p]=p+1-(1+sum((y*y+y-x**3-x*x+2*x)%p==0 for x in range(p) for y in range(p)))
ans=[0,1]
for n in range(2,M+1):
 p=next(p for p in aps if n%p==0);m=n;e=0
 while m%p==0:e+=1;m//=p
 a0=1;a1=aps[p]
 for k in range(2,e+1):a0,a1=a1,aps[p]*a1-(p if p!=389 else 0)*a0
 ans.append(ans[m]*a1)
c=2*arb.pi()/arb(389).sqrt()
def fun(t,analytic):
 q=(-acb(c)*t).exp();s=acb(0)
 for a in reversed(ans[1:]):s=(s+a)*q
 return c*s*t.log(analytic=analytic)**2
print('integrating',flush=True)
v=acb.integral(fun,1,T,abs_tol=arb(2)**-160,rel_tol=arb(2)**-160,eval_limit=100000,depth_limit=100).real
q=(-c).exp()
tailn=q**(M+1)*((M+1)/(1-q)+q/(1-q)**2+(2/c+2/c**2)/(1-q))
qt=(-c*T).exp()
tailt=qt*(T*T+2*T/c+2/c**2)*(1+qt)/(1-qt)**3
v+=arb(0,tailn+tailt)
print('Llead',v.str(40));print('tails',tailn,tailt)
print('BSD ratio',(v/(period*reg)).str(40))
