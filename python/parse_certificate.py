import json, sys, os

inp = sys.argv[1] if len(sys.argv)>1 else "receipts.json"
out = sys.argv[sys.argv.index("--output")+1] if "--output" in sys.argv else "lean/CertifiedSelmer/Proofs/Selmer_389a1_2.lean"

with open(inp, 'r', encoding='utf-8') as fh:
    d = json.load(fh)

os.makedirs(os.path.dirname(out), exist_ok=True)

def q(s):
    # JSON string literal -> safe for Lean as a quoted String
    return json.dumps(str(s))

with open(out, 'w', encoding='utf-8') as f:
    f.write("--! Auto-generated from receipts\n")
    f.write("namespace CertifiedSelmer\n\n")

    f.write("def curve : String := " + q(d.get("curve","")) + "\n")
    f.write("def prime : Nat := " + str(d.get("prime",0)) + "\n")

    lo, hi = d.get("reg_interval", [0.0, 0.0])
    f.write("def regLo : Float := " + str(lo) + "\n")
    f.write("def regHi : Float := " + str(hi) + "\n")

    s = d.get("smith_diagonal", [])
    f.write("def smithDiag : List Nat := [" + ",".join(map(str, s)) + "]\n")

    ar = d.get("analytic_rank", 0)
    f.write("def analyticRank : Nat := " + str(ar) + "\n")

    a, b = d.get("lead_coeff_interval", [0.0, 0.0])
    f.write("def leadLo : Float := " + str(a) + "\n")
    f.write("def leadHi : Float := " + str(b) + "\n")

    f.write("\n-- placeholder theorem; replace with proved predicates later\n")
    f.write("theorem Selmer2inf_vanishes : True := True.intro\n\n")
    f.write("end CertifiedSelmer\n")
