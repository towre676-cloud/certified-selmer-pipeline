"""Replay the complete local Lean target and fail on missing/unsafe axiom reports."""
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]

def check_axiom_log(log, expected, allowed=frozenset()):
    rows = re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)",log)
    if [n for n,_ in rows] != expected:
        raise RuntimeError('missing, duplicate or unexpected axiom report')
    report = {}
    for name, axioms in rows:
        actual = {s.strip() for s in axioms.split(',') if s.strip()}
        if not actual <= allowed:
            raise RuntimeError(f'unsafe axioms for {name}: {actual-allowed}')
        report[name] = sorted(actual)
    return report

def main():
    output = ROOT/'audit'
    output.mkdir(exist_ok=True)
    build = subprocess.run(['lake','build'], cwd=ROOT/'lean', text=True, capture_output=True)
    (output/'lean-build.log').write_text(build.stdout+build.stderr)
    if build.returncode:
        raise RuntimeError('Lean build failed: see audit/lean-build.log')
    proc = subprocess.run(['lake','env','lean','Audit.lean'],cwd=ROOT/'lean',text=True,capture_output=True)
    log = proc.stdout+proc.stderr
    (output/'lean-axioms.log').write_text(log)
    if proc.returncode:
        raise RuntimeError('Lean axiom audit failed')
    expected = re.findall(r'^#print axioms (\S+)',(ROOT/'lean/Audit.lean').read_text(),re.M)
    report = check_axiom_log(log, expected)
    sources = sorted((ROOT/'lean').rglob('*.lean'))
    sources = [p for p in sources if '.lake' not in p.parts]
    record = dict(status='kernel_replay_passed', arithmetic_certified=False,
                  lean_version=subprocess.check_output(['lake','env','lean','--version'],cwd=ROOT/'lean',text=True).strip(),
                  declarations=report,
                  source_sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sources},
                  receipt_raw_sha256=hashlib.sha256((ROOT/'receipts.json').read_bytes()).hexdigest())
    (output/'lean-audit.json').write_text(json.dumps(record,indent=2,sort_keys=True)+'\n')
    print(f'PASS: {len(report)} Lean statements; arithmetic certification remains unavailable')

if __name__ == '__main__': main()
