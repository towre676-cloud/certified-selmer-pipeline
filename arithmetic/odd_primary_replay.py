"""Replay proved odd-primary upper bounds in a pinned Sage/PassageMath backend.
This is theorem-backed CAS computation, NOT a portable independent certificate or Lean proof.
The numerical p-adic BSD ratio alone is never accepted as a proof of Sha triviality.
"""
import argparse
import hashlib
import importlib.metadata
import inspect
import json
from pathlib import Path

SUPPORTED=(5,7,11,13)

def require(ok,message):
    if not ok:raise ValueError(message)

def finite_count(q):
    return 1+sum((y*y+y-x**3-x*x+2*x)%q==0 for x in range(q) for y in range(q))

def irreducibility_witness(p):
    for q in (2,3,5,7,11,13,17,19):
        if q==p:continue
        a=q+1-finite_count(q);d=(a*a-4*q)%p
        if d and pow(d,(p-1)//2,p)==p-1:
            return {'q':q,'a_q':a,'discriminant_mod_p':d}
    raise ValueError('no irreducibility witness found')

def run(primes=SUPPORTED):
    require(bool(primes) and len(set(primes))==len(primes) and
            all(type(p) is int and p in SUPPORTED for p in primes),
            'Only the reviewed primes 5,7,11,13 are enabled; no claim for p=3 or all primes')
    from sage.all__sagemath_schemes import EllipticCurve, QQ, proof, Integer
    import sage.all__sagemath_symbolics  # required by the p-adic regulator implementation
    proof.all(True)
    E=EllipticCurve(QQ,[0,1,1,-2,0])
    rank=E.rank(algorithm='pari',proof=True,use_database=False)
    generators=E.gens(algorithm='pari',proof=True,use_database=False)
    require(rank==2 and E.discriminant()==389 and E.conductor()==389,'curve/rank mismatch')
    sha=E.sha();rho=E.galois_representation();rows=[]
    for p in primes:
        require(Integer(p).is_prime(proof=True),'not prime')
        good=bool(E.has_good_reduction(p));ordinary=bool(E.is_ordinary(p))
        surj=bool(rho.is_surjective(p))
        require(good and ordinary and surj,'theorem applicability not established')
        witness=irreducibility_witness(p)
        exponent=sha.p_primary_bound(p)
        # This call invokes the implemented Stein--Wuthrich/Kato upper-bound theorem.
        # an_padic itself is documented as conjectural equality and is not enough.
        require(exponent==0,'nonzero upper bound: cannot conclude triviality')
        ratio=sha.an_padic(p)
        ratio_hi=sha.an_padic(p,prec=3,use_twists=False)
        require(ratio.precision_absolute()>0 and ratio.valuation()==0,'insufficient unit precision')
        require(ratio_hi.precision_absolute()>=2 and ratio_hi.valuation()==0,'precision replay failed')
        rows.append({'p':p,'a_p':int(E.ap(p)),'good_reduction':good,'ordinary':ordinary,
                     'backend_mod_p_surjective':surj,'frobenius_irreducibility_witness':witness,
                     'auxiliary_multiplicative_prime':389,'minimal_discriminant_valuation':1,
                     'proved_upper_bound_exponent':int(exponent),'proved_order_upper_bound':1,
                     'padic_ratio_default':str(ratio),'default_absolute_precision':int(ratio.precision_absolute()),
                     'padic_ratio_higher_precision':str(ratio_hi),'higher_absolute_precision':int(ratio_hi.precision_absolute()),
                     'conclusion':'Sha[p^infinity] is trivial, by the implemented proved upper bound'})
        print(f'p={p}: proved upper bound 1; precision replay {ratio_hi}',flush=True)
    try:
        sha.p_primary_bound(3)
    except NotImplementedError as exc:
        prime_three={'status':'backend_not_implemented','exception':str(exc),
                     'Sha3_triviality_proved':False}
    else:
        raise RuntimeError('Unexpected new p=3 support requires separate mathematical review')
    paths={Path(inspect.getsourcefile(type(sha))),Path(inspect.getsourcefile(type(E)))}
    from sage.schemes.elliptic_curves import padics, padic_lseries, mod_sym_num
    paths.update(Path(m.__file__) for m in (padics,padic_lseries,mod_sym_num))
    return {'status':'theorem_backed_CAS_replay_passed','curve_ainvs':[0,1,1,-2,0],
            'rank':int(rank),'rank_algorithm':'pari, proof=True, use_database=False',
            'generators_found':[str(P) for P in generators],
            'packages':{p:importlib.metadata.version(p) for p in
                ['passagemath-schemes','passagemath-eclib','passagemath-symbolics','passagemath-pari']},
            'source_sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(paths)},
            'rows':rows,'formal_Lean_proof':False,'portable_independent_certificate':False,
            'all_Sha_triviality_proved':False,'prime_3_status':prime_three,
            'unbounded_primes_status':'not established by this replay',
            'trust_boundary':'Sage/PassageMath arithmetic implementation, its precision analysis, '
                'and the cited Stein--Wuthrich/Kato theorem; not inferred from an approximate BSD equality'}

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output',default=str(Path(__file__).with_name('odd_primary_replay.json')))
    args=p.parse_args();record=run()
    record['runner_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    Path(args.output).write_text(json.dumps(record,indent=2)+'\n')
    print('Four prime-primary bounds replayed; full Sha and complete formalization remain open')

if __name__=='__main__':main()
