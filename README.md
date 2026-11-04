# certified-selmer-pipeline

**Current status: a curve-specific arithmetic proof and rigorous numerical replay; end-to-end Lean Selmer certification remains open.**

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

## Curve-specific arithmetic follow-up

[The new arithmetic proof](arithmetic/CURVE389_PROOF.md) establishes rank two, a full Mordell–Weil basis, 2-Selmer dimension two and 2-primary Sha vanishing using standard mathematical theorems with independently checked curve-specific calculations. It supplies rigorous regulator, period and L-leading-coefficient enclosures. A separate fresh PARI full descent agrees.

This is a mathematical proof with executable arithmetic checks, not a complete Lean formalization. There are now 19 limited kernel-replayed statements. Full Sha triviality remains unproved, and the generic arithmetic proof generator continues to fail closed.

```bash
python3 -m pip install -r arithmetic/requirements.txt
python3 arithmetic/verify_389.py
python3 arithmetic/pari_replay.py
```
