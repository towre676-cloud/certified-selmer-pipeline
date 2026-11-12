import importlib.util
import unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location("cubic_certificate_scout",ROOT/"arithmetic"/"cubic_certificate_scout.py")
M=importlib.util.module_from_spec(spec)
spec.loader.exec_module(M)

class CubicCertificateScoutTests(unittest.TestCase):
    def test_five_cubic_fields(self):
        report=M.replay()
        self.assertEqual([r["discriminant_prime"] for r in report["examples"]],
                         [37,101,197,269,389])
        self.assertTrue(all(r["certificate"]["maximal_power_order"] for r in report["examples"]))

if __name__=="__main__":
    unittest.main()
