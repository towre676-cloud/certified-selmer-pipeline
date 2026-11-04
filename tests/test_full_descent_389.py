import copy
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'arithmetic'))
from full_descent_389 import verify, load, mul, norm, InvalidCertificate

class FullDescent389Tests(unittest.TestCase):
    def setUp(self):self.c=load(ROOT/'arithmetic/full_descent_389.json')

    def test_complete_finite_witnesses(self):
        r=verify(self.c)
        self.assertEqual(r['field_discriminant'],1556)
        self.assertEqual(r['local_images_on_P_Q'],{'real':[1,0],'2':[1,1],'389':[1,0]})
        self.assertFalse(r['formal_arithmetic_certified'])

    def test_changed_point_rejected(self):
        self.c['covers'][1]['point'][0]=2
        with self.assertRaises(InvalidCertificate):verify(self.c)

    def test_fabricated_unit_rejected(self):
        self.c['units'][0][0]+=1
        with self.assertRaises(InvalidCertificate):verify(self.c)

    def test_corrupted_local_square_root_rejected(self):
        for place in ['two_product_square_mod8','389_Q_roots']:
            c=copy.deepcopy(self.c);c['local_witnesses'][place][0]+=1
            with self.assertRaises(InvalidCertificate):verify(c)

    def test_changed_field_and_curve_rejected(self):
        for key in ['g','F','ainvs']:
            c=copy.deepcopy(self.c);c[key][0]+=1
            with self.assertRaises(InvalidCertificate):verify(c)

    def test_bad_cover_square_and_norm_rejected(self):
        for key in ['delta','z']:
            c=copy.deepcopy(self.c);c['covers'][0][key][0]+=1
            with self.assertRaises(InvalidCertificate):verify(c)

    def test_schema_no_extra_arithmetic_claims(self):
        self.c['rank_certified']=True
        with self.assertRaises(InvalidCertificate):verify(self.c)

    def test_bools_not_integers(self):
        self.c['ainvs'][0]=False
        with self.assertRaises(InvalidCertificate):verify(self.c)

    def test_false_root_bracket_and_minkowski_bound_rejected(self):
        c=copy.deepcopy(self.c);c['brackets'][0]=['0','1']
        with self.assertRaises(InvalidCertificate):verify(c)
        c=copy.deepcopy(self.c);c['minkowski_square'][0]=6000
        with self.assertRaises(InvalidCertificate):verify(c)

    def test_duplicate_key_rejected(self):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/'c.json';p.write_text('{"g":1,"g":2}')
            with self.assertRaises(InvalidCertificate):load(p)

    def test_optimized_python_retains_checks(self):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/'c.json';self.c['units'][0][0]+=1;p.write_text(json.dumps(self.c))
            r=subprocess.run([sys.executable,'-O',str(ROOT/'arithmetic/full_descent_389.py'),str(p)],capture_output=True)
            self.assertNotEqual(r.returncode,0)

    def test_cubic_arithmetic_independent_evaluation(self):
        # Check the reduction formula and determinant norm against a separate
        # Sylvester resultant in Sympy, when available (not a runtime dependency).
        try:import sympy as s
        except ImportError:self.skipTest('optional independent Sympy check')
        t=s.Symbol('t');g=t**3-t*t-9*t+11
        samples=[tuple(row) for row in self.c['units']]+[(-3,1,0),(2,-2,0),(6,-2,0)]
        for a in samples:
            aa=sum(v*t**i for i,v in enumerate(a))
            self.assertEqual(norm(a),int(s.resultant(g,aa,t)))
            for b in samples:
                bb=sum(v*t**i for i,v in enumerate(b));r=s.Poly(s.rem(aa*bb,g,t),t)
                self.assertEqual(mul(a,b),tuple(int(r.nth(i)) for i in range(3)))

if __name__=='__main__':unittest.main()
