import importlib.util
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
ARITH = ROOT / "arithmetic"
sys.path.insert(0, str(ARITH))

PERFECTJET_AVAILABLE = importlib.util.find_spec("perfectjet") is not None
if PERFECTJET_AVAILABLE:
    spec = importlib.util.spec_from_file_location(
        "perfectjet_cubic_bridge", ARITH/"perfectjet_bridge.py")
    B = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(B)
else:
    B = None


@unittest.skipUnless(PERFECTJET_AVAILABLE, "PerfectJet is exercised by the dedicated pinned bridge workflow")
class PerfectJetCubicBridgeTests(unittest.TestCase):
    def test_finite_arithmetic_sweep(self):
        report = B.deterministic_arithmetic_sweep()
        self.assertEqual(report["elements_checked"], 125)
        self.assertEqual(report["multiplication_cases"], 1625)

    def test_retained_certificate(self):
        report = B.retained_certificate_replay()
        self.assertEqual(report["power_basis_discriminant"], "1556")
        self.assertEqual(
            report["principal_prime_norms"],
            {"beta_minus_3": "-2", "beta_minus_2": "3"})
        self.assertEqual(report["chord_square_relation"], ["16", "0", "0"])
        self.assertTrue(all(r["cover_identity_replayed"] for r in report["covers"]))

    def test_trace_matrix(self):
        self.assertEqual(
            B.K.trace_matrix(),
            [[3, 1, 19], [1, 19, -5], [19, -5, 155]])


if __name__ == "__main__":
    unittest.main(verbosity=2)
