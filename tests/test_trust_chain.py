import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/'python'))
from verify_receipts import load_receipt, VerificationError
from parse_certificate import generate, render
from exact_certificates import curve_facts, verify_smith
from audit_lean import check_axiom_log

class TrustChainTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.path = Path(self.tmp.name)/'receipt.json'
        self.raw = (ROOT/'receipts.json').read_text()

    def write(self, d, rehash=True):
        if rehash:
            payload = dict(d)
            payload.pop('merkle_root', None)
            d['merkle_root'] = hashlib.sha256(json.dumps(payload, separators=(',',':')).encode()).hexdigest()
        self.path.write_text(json.dumps(d))
        return self.path

    def test_main_receipt_exact(self):
        d = load_receipt(ROOT/'receipts.json')
        self.assertEqual(str(d['reg_interval'][0]), '7623008897157181/50000000000000000')

    def test_broken_sample_rejected(self):
        with self.assertRaises(VerificationError):
            load_receipt(ROOT/'receipts/selmer_389a1_p2.json')

    def test_mutation_without_new_digest_rejected(self):
        d = json.loads(self.raw); d['analytic_rank'] = 3
        with self.assertRaises(VerificationError):
            load_receipt(self.write(d, False))

    def test_rehashed_fabrication_cannot_prove_arithmetic(self):
        d = json.loads(self.raw); d['analytic_rank'] = 999
        p = self.write(d)
        self.assertEqual(load_receipt(p)['analytic_rank'], 999)
        with self.assertRaises(VerificationError):
            generate(p, Path(self.tmp.name)/'out.lean', 'arithmetic')

    def test_rejected_inputs(self):
        for key,value in [('curve','evil"\naxiom fake : False'), ('prime',True),
                          ('smith_diagonal',[True,1]), ('analytic_rank',-1),
                          ('reg_interval',[1,1]), ('lead_coeff_interval',[-2,-1]),
                          ('reg_interval',['1','2']), ('unexpected',1)]:
            with self.subTest(key=key,value=value):
                d = json.loads(self.raw); d[key] = value
                with self.assertRaises(VerificationError):
                    load_receipt(self.write(d))

    def test_duplicate_keys_rejected(self):
        self.path.write_text(self.raw.replace('"prime":2', '"prime":2,"prime":2'))
        with self.assertRaises(VerificationError): load_receipt(self.path)

    def test_nonfinite_rejected(self):
        for token in ('NaN','Infinity','-Infinity','1e999'):
            self.path.write_text(self.raw.replace('0.7593165002884267',token))
            with self.assertRaises(VerificationError): load_receipt(self.path)

    def test_generator_does_not_overwrite_on_failure(self):
        out = Path(self.tmp.name)/'out.lean'; out.write_text('sentinel')
        with self.assertRaises(VerificationError): generate(ROOT/'receipts.json',out,'arithmetic')
        self.assertEqual(out.read_text(),'sentinel')

    def test_generated_file_is_current(self):
        self.assertEqual(render(load_receipt(ROOT/'receipts.json')),
            (ROOT/'lean/CertifiedSelmer/Proofs/Receipt_389a1_2.lean').read_text())

    def test_default_cli_fails_closed(self):
        proc = subprocess.run([sys.executable,'python/parse_certificate.py'],cwd=ROOT,capture_output=True)
        self.assertEqual(proc.returncode,2)
        proc = subprocess.run([sys.executable,'python/verify_receipts.py','--require-arithmetic'],cwd=ROOT,capture_output=True)
        self.assertEqual(proc.returncode,2)

    def test_sage_runner_refuses_fixture_copy(self):
        before = (ROOT/'receipts.json').read_bytes()
        proc = subprocess.run([sys.executable,'sage/selmer_ci_runner.sage'],cwd=ROOT,capture_output=True)
        self.assertNotEqual(proc.returncode,0)
        self.assertEqual(before,(ROOT/'receipts.json').read_bytes())

    def test_smith_valid_and_invalid(self):
        identity = [[1,0],[0,1]]
        self.assertTrue(verify_smith([[1,1],[0,1]],identity,[[1,-1],[0,1]],[1,1]))
        for a,u,v,d in [([[2,0],[0,1]],identity,identity,[1,1]),
                         (identity,[[2,0],[0,1]],identity,[2,2]),
                         ([[2,0],[0,3]],identity,identity,[2,3])]:
            with self.assertRaises(VerificationError): verify_smith(a,u,v,d)

    def test_axiom_log_rejects_unsafe_or_missing_reports(self):
        self.assertEqual(check_axiom_log("'A' does not depend on any axioms", ['A']), {'A': []})
        for log in ("", "'A' depends on axioms: [sorryAx]",
                    "'A' depends on axioms: [Lean.ofReduceBool]",
                    "'A' depends on axioms: [unprovedArithmetic]"):
            with self.assertRaises(RuntimeError): check_axiom_log(log, ['A'])

    def test_core_axiom_audit_requires_empty_lists(self):
        for axiom in ('propext', 'Classical.choice', 'Quot.sound'):
            log = f"'A' depends on axioms: [{axiom}]"
            with self.assertRaises(RuntimeError):
                check_axiom_log(log, ['A'])
            self.assertEqual(check_axiom_log(log, ['A'], allowed={axiom}),
                             {'A': [axiom]})
        with self.assertRaises(RuntimeError):
            check_axiom_log("'A' depends on axioms: [sorryAx]", ['A'],
                            allowed={'propext', 'Classical.choice', 'Quot.sound'})

    def test_legacy_digest_does_not_bind_decimal_tokens(self):
        # Deliberately documents a legacy limitation; NOT a stronger digest claim.
        self.path.write_text(self.raw.replace('0.15246017794314362',
                                              '0.1524601779431436200000000001'))
        changed = load_receipt(self.path)
        original = load_receipt(ROOT/'receipts.json')
        self.assertNotEqual(changed['reg_interval'][0],original['reg_interval'][0])

    def test_curve_obstruction(self):
        d = curve_facts()
        self.assertEqual(d['rational_two_torsion_order'],1)
        self.assertFalse(d['selmer_certified'])

if __name__ == '__main__': unittest.main()
