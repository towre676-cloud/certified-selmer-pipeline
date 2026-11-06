# Integrated full-descent witnesses: completed verification

Base: PR #1 head `7ca095e71ccbaf3dbb81d0aebe101c1c77ed7036`.

The previously uncompiled descent draft is now the default-build module
`CertifiedSelmer.FullDescent389`. Fresh installation of official Lean 4.20.0
and a startup-path compatibility shim permits actual kernel replay. All 42
audited declarations have empty transitive axiom lists, including all 23 new
finite descent facts. The combined Python suite passes 35 tests, preserving
the prior arithmetic, numerical enclosure, PARI and trust-boundary checks.

The new formal facts include norm and unit identities, rational norm-cover
witnesses, equality of the product class with P+Q, all 512 modulo-eight
square candidates, local square witnesses at 389 and real root-bracket signs.
The portable Python certificate uses only the standard library, and runs in
CI as well as in corruption-rejection tests. The generic receipt generator
continues to reject unsupported arithmetic claims.

Evidence: `audit/lean-audit.json`, `audit/lean-axioms.log`,
`audit/lean-build.log`, `audit/descent-toolchain.json`,
`audit/full-descent-finite-checks.json`, `audit/full-descent-integration-tests.log`.
All source hashes in the Lean audit refer to the integrated current sources.

The written full-descent proof establishes rank two, 2-Selmer dimension two
and 2-primary Sha vanishing using standard mathematical theorems. This pass
closes the finite-Lean-witness compilation and integration gap. It does **not**
complete an end-to-end formal proof of rank or Sha: the cubic-field/maximal-order,
ideal/class-group, local-field and Kummer-exact-sequence bridges remain outside
Lean. No extra axioms were inserted to conceal these obligations. See
`docs/FULL_2_DESCENT_389.md` for the full conventional proof and formal boundary.

The earlier numerical and point-saturation proof is preserved and tested;
this update does not infer full Sha triviality or BSD from an enclosure.
