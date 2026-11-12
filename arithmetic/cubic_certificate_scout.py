#!/usr/bin/env python3
"""Reusable cubic power-order certificate scout beyond 389a1."""
from __future__ import annotations
import json
from perfectjet.cubic_certificate_search import maximal_power_order_pattern

EXAMPLES = {
    "37": [1,-1,-3,1],
    "101": [2,0,-4,1],
    "197": [2,-2,-4,1],
    "269": [1,-3,-5,1],
    "389": [11,-9,-1,1],
}


def replay():
    rows=[]
    for p,coefficients in EXAMPLES.items():
        report=maximal_power_order_pattern(coefficients)
        if report.get("status")!="certified_pattern":
            raise AssertionError((p,report))
        if report["discriminant"]!=4*int(p):
            raise AssertionError((p,report["discriminant"]))
        rows.append({"discriminant_prime":int(p),"certificate":report})
    return {
        "schema":"certified-selmer-pipeline/cubic-certificate-scout/1",
        "examples":rows,
        "scope":"Reusable maximal-power-order pattern, not class-number, Selmer, or Sha proofs.",
    }


if __name__=="__main__":
    print(json.dumps(replay(),indent=2,sort_keys=True))
