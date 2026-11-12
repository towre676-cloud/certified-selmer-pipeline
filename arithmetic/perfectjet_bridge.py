#!/usr/bin/env python3
"""Independent PerfectJet replay of the 389a1 cubic arithmetic.

This bridge does not prove irreducibility, maximality, class number one,
local-field statements, Selmer exactness, rank, or Sha vanishing. It compares
the maintained stdlib quotient arithmetic and retained finite witnesses against
PerfectJet's generic monogenic quotient-algebra engine.
"""
from __future__ import annotations

import argparse
import json
import sys
from fractions import Fraction as Q
from itertools import product
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(HERE))

import full_descent_389 as D

from perfectjet.quotient_algebra import MonogenicQuotient

K = MonogenicQuotient([11, -9, -1, 1])


def as_tuple(values):
    return tuple(Q(x) for x in values)


def compare_element(a):
    a = tuple(int(x) for x in a)
    return {
        "element": list(a),
        "trace_native": D.trace(a),
        "trace_perfectjet": str(K.trace(a)),
        "norm_native": D.norm(a),
        "norm_perfectjet": str(K.norm(a)),
        "multiplication_matrix_perfectjet": [
            [str(x) for x in row] for row in K.multiplication_matrix(a)
        ],
    }


def deterministic_arithmetic_sweep():
    """Compare multiplication, norm, and trace on a fixed finite cube."""
    elems = list(product(range(-2, 3), repeat=3))
    multiplication_cases = 0
    for a in elems:
        if K.norm(a) != D.norm(a):
            raise AssertionError(("norm", a, K.norm(a), D.norm(a)))
        if K.trace(a) != D.trace(a):
            raise AssertionError(("trace", a, K.trace(a), D.trace(a)))
    # Pair every element against a smaller deterministic probe set. This gives
    # 125*13 exact products without making CI unnecessarily quadratic.
    probes = [
        (1, 0, 0), (0, 1, 0), (0, 0, 1),
        (-3, 1, 0), (-2, 1, 0),
        (2, -2, 0), (6, -2, 0),
        (1, 1, 1), (-1, 1, 1), (2, 0, -1),
        (0, 2, 1), (1, -2, 2), (-2, -1, 1),
    ]
    for a in elems:
        for b in probes:
            left = as_tuple(D.mul(a, b))
            right = K.multiply(a, b)
            if left != right:
                raise AssertionError(("multiply", a, b, left, right))
            multiplication_cases += 1
    return {
        "elements_checked": len(elems),
        "multiplication_cases": multiplication_cases,
        "probe_count": len(probes),
    }


def retained_certificate_replay():
    certificate = D.load(HERE / "full_descent_389.json")
    native = D.verify(certificate)
    gram = [[int(x) for x in row] for row in K.trace_matrix()]
    if gram != native["trace_pairing"]:
        raise AssertionError(("trace pairing", gram, native["trace_pairing"]))
    if K.discriminant() != native["field_discriminant"]:
        raise AssertionError(("discriminant", K.discriminant(), native["field_discriminant"]))

    pi = tuple(certificate["prime_generators"]["2"])
    rho = tuple(certificate["prime_generators"]["3"])
    if (K.norm(pi), K.norm(rho)) != (Q(-2), Q(3)):
        raise AssertionError("principal prime norm witnesses changed")

    covers = []
    for row in certificate["covers"]:
        x, y = row["point"]
        delta = tuple(row["delta"])
        z = tuple(row["z"])
        X = 4*x
        lhs = K.multiply(delta, K.power(z, 2))
        rhs = K.element([X+2, -2, 0])  # X - theta, theta = 2 beta - 2.
        if lhs != rhs:
            raise AssertionError(("cover", row["point"], lhs, rhs))
        covers.append({
            "point": row["point"],
            "delta_norm": str(K.norm(delta)),
            "cover_identity_replayed": True,
        })

    units = []
    for delta, unit in zip((tuple(r["delta"]) for r in certificate["covers"]),
                           (tuple(u) for u in certificate["units"])):
        if K.norm(unit) != 1:
            raise AssertionError(("unit norm", unit, K.norm(unit)))
        normalized = K.multiply(K.power(pi, 4), unit)
        if normalized != K.element(delta):
            raise AssertionError(("unit normalization", delta, unit, normalized))
        units.append({
            "unit": list(unit),
            "norm": "1",
            "pi4_times_unit_equals_delta": True,
        })

    chord = K.multiply(
        K.multiply(tuple(certificate["covers"][0]["delta"]),
                   tuple(certificate["covers"][1]["delta"])),
        tuple(certificate["covers"][2]["delta"]))
    if chord != K.element([16, 0, 0]):
        raise AssertionError(("chord relation", chord))

    return {
        "trace_pairing": gram,
        "power_basis_discriminant": str(K.discriminant()),
        "principal_prime_norms": {
            "beta_minus_3": str(K.norm(pi)),
            "beta_minus_2": str(K.norm(rho)),
        },
        "covers": covers,
        "units": units,
        "chord_square_relation": [str(x) for x in chord],
        "native_certificate_status": native["status"],
    }


def receipt():
    return {
        "schema": "certified-selmer-pipeline/perfectjet-cubic-bridge/1",
        "modulus": ["11", "-9", "-1", "1"],
        "arithmetic_sweep": deterministic_arithmetic_sweep(),
        "retained_certificate": retained_certificate_replay(),
        "perfectjet_quotient_receipt": K.receipt(),
        "proof_boundary": [
            "This is exact quotient-algebra replay, not a number-field maximal-order theorem.",
            "Irreducibility and the identification with the actual cubic number field remain separate.",
            "The field-discriminant theorem in Mathlib requires maximality of the power order; this bridge only recomputes the power-basis trace discriminant.",
            "No class-number, unit-rank completeness, local Kummer image, Selmer, Mordell-Weil rank, or Sha conclusion follows from this bridge alone.",
        ],
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output")
    args = parser.parse_args()
    data = json.dumps(receipt(), indent=2, sort_keys=True) + "\n"
    if args.output:
        Path(args.output).write_text(data)
    else:
        print(data, end="")


if __name__ == "__main__":
    main()
