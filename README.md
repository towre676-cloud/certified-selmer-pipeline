# certified-selmer-pipeline

**Current status: receipt consistency and limited formal facts, not certified Selmer vanishing.**

The historical 389a1 receipts contain unverified arithmetic assertions. The old Sage runner copied a fixture, and the old Lean generator proved only `True`. The corrected interface refuses arithmetic certification until actual descent witnesses and arithmetic proofs are supplied.

See [the trust-chain audit and proof architecture](docs/TRUST_CHAIN_AUDIT.md) for the exact target, missing mathematical inputs, and the obstruction to applying PerfectPower's rational two-isogeny models directly to 389a1.

```bash
python3 -m unittest discover -s tests -v
python3 python/verify_receipts.py
python3 python/parse_certificate.py --scope receipt
python3 python/exact_certificates.py
python3 python/audit_lean.py  # requires Lean/Lake 4.20.0 on PATH
```

The verifier checks the historical decoded-payload digest and exact decimal ordering. It does not prove enclosure, rank, Smith normal form, Selmer completeness, or Sha vanishing. The damaged sample receipt is retained and deliberately rejected. A raw receipt hash is also recorded in the local audit; the historical digest does not bind exact decimal spelling or authenticate a producer.

The following commands must fail until a genuine arithmetic backend exists:

```bash
python3 python/verify_receipts.py --require-arithmetic
python3 python/parse_certificate.py
sage sage/selmer_ci_runner.sage
```

Explicit receipt scope emits kernel-checkable literal inequalities, never a Selmer theorem. A successful CI run means only those limited facts and the rejection tests passed.
