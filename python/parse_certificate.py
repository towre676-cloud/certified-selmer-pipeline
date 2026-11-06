"""Generate receipt facts only on an explicit limited-scope request."""
import argparse
import os
from pathlib import Path
import tempfile
from verify_receipts import load_receipt, require_arithmetic

def render(d):
    lines = ['-- Generated receipt syntax facts. No enclosure or Selmer theorem.',
             'import CertifiedSelmer.Predicates', 'namespace CertifiedSelmer.Receipt389']
    for name, key in (('reg', 'reg_interval'), ('lead', 'lead_coeff_interval')):
        a, b = d[key]
        lines += [f'def {name} : RationalInterval :=',
                  f'  ⟨{a.numerator}, {a.denominator}, {b.numerator}, {b.denominator}⟩',
                  f'theorem {name}_wellFormed : {name}.WellFormed := by decide']
    lines += [f'def assertedAnalyticRank : Nat := {d["analytic_rank"]}',
              'def assertedSmithDiagonal : List Nat := [1, 1]',
              'theorem assertedSmith_identity : assertedSmithDiagonal = [1, 1] := rfl',
              'end CertifiedSelmer.Receipt389', '']
    return '\n'.join(lines)

def generate(inp, out, scope):
    d = load_receipt(inp)
    if scope != 'receipt':
        require_arithmetic(d)
    content = render(d)
    out = Path(out)
    out.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(mode='w', dir=out.parent, delete=False) as f:
        tmp = f.name
        f.write(content)
    os.replace(tmp, out)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('receipt', nargs='?', default='receipts.json')
    parser.add_argument('--output', default='lean/CertifiedSelmer/Proofs/Receipt_389a1_2.lean')
    parser.add_argument('--scope', choices=('arithmetic', 'receipt'), default='arithmetic')
    args = parser.parse_args()
    try:
        generate(args.receipt, args.output, args.scope)
    except (ValueError, OSError, TypeError) as exc:
        parser.exit(2, f'REJECTED: {exc}\n')
    print('Generated receipt facts only; no arithmetic certification')

if __name__ == '__main__':
    main()
