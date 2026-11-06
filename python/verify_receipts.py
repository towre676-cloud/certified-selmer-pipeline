"""Legacy receipt integrity and exact decimal consistency; NOT arithmetic certification."""
import argparse
from decimal import Decimal
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import re

class VerificationError(ValueError):
    pass

def require(condition, message):
    if not condition:
        raise VerificationError(message)

def unique_object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, f'duplicate JSON key: {key}')
        result[key] = value
    return result

def reject_constant(value):
    raise VerificationError(f'nonfinite JSON constant: {value}')

def load_receipt(path):
    raw = Path(path).read_text(encoding='utf-8')
    # Historical binary64 digest convention ONLY for compatibility.
    # Mathematical facts use separate exact decimal parsing below.
    opts = dict(object_pairs_hook=unique_object, parse_constant=reject_constant)
    legacy = json.loads(raw, **opts)
    d = json.loads(raw, parse_float=Decimal, **opts)
    keys = {'curve', 'prime', 'merkle_root', 'reg_interval', 'smith_diagonal',
            'analytic_rank', 'lead_coeff_interval'}
    require(isinstance(d, dict) and set(d) == keys, 'unexpected receipt schema')
    require(d['curve'] == '389a1', 'wrong curve')
    require(type(d['prime']) is int and d['prime'] == 2, 'wrong prime')
    require(type(d['analytic_rank']) is int and d['analytic_rank'] >= 0,
            'invalid asserted analytic rank')
    require(isinstance(d['smith_diagonal'], list) and
            all(type(x) is int for x in d['smith_diagonal']) and
            d['smith_diagonal'] == [1, 1], 'unexpected asserted Smith diagonal')
    root = legacy.pop('merkle_root')
    require(isinstance(root, str) and re.fullmatch(r'[0-9a-f]{64}', root),
            'invalid SHA-256 format')
    try:
        canonical = json.dumps(legacy, separators=(',', ':'), allow_nan=False).encode()
    except ValueError as exc:
        raise VerificationError('legacy digest contains nonfinite values') from exc
    require(hashlib.sha256(canonical).hexdigest() == root, 'payload digest mismatch')
    for key in ('reg_interval', 'lead_coeff_interval'):
        pair = d[key]
        require(isinstance(pair, list) and len(pair) == 2, f'bad {key} shape')
        require(all(type(x) in (int, Decimal) for x in pair), f'bad {key} endpoints')
        a, b = map(Fraction, pair)
        require(0 < a < b, f'{key} must have positive ordered endpoints')
        d[key] = (a, b)
    return d

def require_arithmetic(_receipt):
    raise VerificationError('arithmetic certification unavailable: no descent/local-condition '
                            'certificate, MW independence proof, or enclosure derivation')

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('receipt', nargs='?', default='receipts.json')
    parser.add_argument('--require-arithmetic', action='store_true')
    args = parser.parse_args()
    try:
        d = load_receipt(args.receipt)
        if args.require_arithmetic:
            require_arithmetic(d)
    except (ValueError, OSError, TypeError) as exc:
        parser.exit(2, f'REJECTED: {exc}\n')
    print('PASS: legacy digest and exact decimal consistency only; arithmetic NOT certified')

if __name__ == '__main__':
    main()
