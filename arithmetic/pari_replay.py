"""Fresh PARI 2.15.4 cross-check; its arithmetic implementation is a trusted CAS layer."""
from cypari import pari
from pathlib import Path
import json

def run():
    pari('default(realprecision,100); setrand(1)')
    pari('E=ellinit([0,1,1,-2,0]); r=ellrank(E); C=ell2cover(E)')
    assert [int(x) for x in pari('r[1..3]')]==[2,2,0]
    assert int(pari('#C'))==2
    assert int(pari('elltors(E)[1]'))==1
    assert int(pari('ellglobalred(E)[1]'))==389
    pari('b=bnfinit(x^3-x^2-9*x+11,1)')
    assert int(pari('bnfcertify(b)'))==1
    assert int(pari('b.no'))==1
    pari('m=msfromell(E,1)')
    assert int(pari('mseval(m[1],m[2],[0,oo])'))==0
    assert int(pari('ellrootno(E)'))==1
    for k in [1,2]:
        assert int(pari(f'subst(C[{k}][1],x,0)'))==1
        assert int(pari(f'ellisoncurve(E,substvec(C[{k}][2],[x,y],[0,1]))'))==1
    return {'PARI_version':str(pari('version()')),'rank_result':str(pari('r')),
        'two_cover_basis':str(pari('C')),'two_cover_count':2,
        'cover_witnesses':[str(pari(f'substvec(C[{k}][2],[x,y],[0,1])')) for k in [1,2]],
        'class_number':1,'bnfcertify':1,'exact_modular_symbol_0_to_infinity':0,
        'global_root_number':1,'torsion_order':1,'conductor':389,
        'height_matrix_crosscheck':str(pari('ellheightmatrix(E,[[0,0],[1,0]])')),
        'L_second_derivative_crosscheck':str(pari('ellL1(E,2)')),
        'full_sha_triviality_proved':False,'Lean_arithmetic_replay':False}

if __name__=='__main__':
    out=Path(__file__).with_name('pari_replay.json');out.write_text(json.dumps(run(),indent=2)+'\n')
    print('Fresh PARI rank, cover, class-number and modular-symbol checks passed')
