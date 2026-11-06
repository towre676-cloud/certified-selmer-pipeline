"""Replay actual rational-curve theorems and audit their transitive axioms."""
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT=Path(__file__).resolve().parent
OUTPUT=ROOT.parent/'audit'/'mathlib389'
EXPECTED_MATHLIB='c211948581bde9846a99e32d97a03f0d5307c31e'
sys.path.insert(0,str(ROOT.parent/'python'))
from audit_lean import check_axiom_log

def command(args, log):
    result=subprocess.run(args,cwd=ROOT,text=True,capture_output=True)
    (OUTPUT/log).write_text(result.stdout+result.stderr)
    if result.returncode:raise RuntimeError(f'{log} failed; see audit/mathlib389/{log}')
    return result.stdout+result.stderr

def main():
    OUTPUT.mkdir(parents=True,exist_ok=True)
    revision=subprocess.check_output(['git','-C',str(ROOT/'.lake/packages/mathlib'),
                                     'rev-parse','HEAD'],text=True).strip()
    if revision!=EXPECTED_MATHLIB:raise RuntimeError('unexpected Mathlib revision')
    target=ROOT/'.lake/build/lib/lean/Curve389.olean'
    target.parent.mkdir(parents=True,exist_ok=True)
    command(['lake','env','lean','-o',str(target),'Curve389.lean'],'build.log')
    axioms=command(['lake','env','lean','Audit.lean'],'axioms.log')
    names=re.findall(r'^#print axioms (\S+)',(ROOT/'Audit.lean').read_text(),re.M)
    reports=check_axiom_log(axioms,names, allowed={'propext','Classical.choice','Quot.sound'})
    sources=['Curve389.lean','Audit.lean','lakefile.toml','lake-manifest.json','lean-toolchain','replay.py']
    record={'status':'kernel_replay_passed','mathlib_revision':revision,
            'lean_version':subprocess.check_output(['lake','env','lean','--version'],cwd=ROOT,text=True).strip(),
            'declarations':reports,'actual_rational_curve_two_primary_torsion_formalized':True,
            'Sha_theorem_formalized':False,'rank_theorem_formalized':False,
            'source_sha256':{n:hashlib.sha256((ROOT/n).read_bytes()).hexdigest() for n in sources}}
    (OUTPUT/'receipt.json').write_text(json.dumps(record,indent=2,sort_keys=True)+'\n')
    print(f'PASS: {len(names)} actual-curve declarations; standard axiom allowlist passed')

if __name__=='__main__':main()
