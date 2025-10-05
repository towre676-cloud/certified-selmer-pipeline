import json, hashlib, os, sys

# Load receipts bundle (text + parse)
raw = open("receipts.json","rb").read()
d = json.loads(raw)

# Canonical payload: same JSON but without `merkle_root`
payload = dict(d)
payload.pop("merkle_root", None)
canon = json.dumps(payload, separators=(',',':')).encode('utf-8')
computed = hashlib.sha256(canon).hexdigest()

# If embedded root missing or wrong, fail with a helpful message
embedded = d.get("merkle_root")
if embedded != computed:
    print("[error] Merkle root mismatch (canonical)")
    print("  expected:", embedded)
    print("  computed:", computed)
    sys.exit(2)

# Basic interval checks (strict positivity where required)
def ok_interval(key, positive=True):
    a,b = d[key]
    if not (a < b):
        print(f"[error] {key} not strictly increasing: {a} !< {b}")
        sys.exit(3)
    if positive and not (a > 0):
        print(f"[error] {key} lower bound not > 0: {a}")
        sys.exit(4)
    return a,b

regLo, regHi = ok_interval("reg_interval", positive=True)
leadLo, leadHi = ok_interval("lead_coeff_interval", positive=True)
smith = d.get("smith_diagonal", [])
if smith != [1,1]:
    print("[error] smith_diagonal != [1,1]:", smith)
    sys.exit(5)

# Emit Lean predicates module
out = "lean/CertifiedSelmer/Predicates.lean"
os.makedirs(os.path.dirname(out), exist_ok=True)
with open(out, "w", encoding="utf-8") as f:
    f.write("--! auto-generated verified predicates from receipts.json\n")
    f.write("namespace CertifiedSelmer\n\n")
    f.write(f"def regLoV : Float := {regLo}\n")
    f.write(f"def leadLoV : Float := {leadLo}\n")
    f.write(f"def smithDiagV : List Nat := [1,1]\n\n")
    f.write("def regPositiveV : Prop := regLoV > 0\n")
    f.write("def leadPositiveV : Prop := leadLoV > 0\n")
    f.write("def smithIdentityV : Prop := smithDiagV = [1,1]\n\n")
    f.write("end CertifiedSelmer\n")
print("[ok] wrote lean/CertifiedSelmer/Predicates.lean and verified receipts")
