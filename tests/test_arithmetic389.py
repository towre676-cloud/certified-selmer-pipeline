import json
from decimal import Decimal
from pathlib import Path
import sys
import unittest
from fractions import Fraction as Q
from flint import arb, ctx
from cypari import pari
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'arithmetic'))
from verify_389 import run, exact_checks, height, leading_coefficient, finite_count, interval
from pari_replay import run as pari_run

def decode(d): return interval(d['lo'],d['hi'])

class Curve389Tests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):cls.record=run()

    def test_descent_arithmetic_inputs(self):
        e=self.record['exact']
        self.assertEqual(e['field_discriminant'],1556)
        self.assertEqual(e['norm_witnesses'],{'beta_minus_3':-2,'beta_minus_2':3})
        self.assertEqual(e['minkowski_bound_squared_comparison'],[6224,6561])

    def test_pari_descent_and_exact_symbol(self):
        r=pari_run()
        self.assertEqual(r['two_cover_count'],2)
        self.assertEqual(r['class_number'],1)
        self.assertEqual(r['exact_modular_symbol_0_to_infinity'],0)

    def test_fourier_coefficients_independent_of_pari(self):
        pari('E=ellinit([0,1,1,-2,0])')
        actual=[int(x) for x in pari('ellan(E,256)')]
        self.assertEqual(self.record['fourier_coefficients'],actual)

    def test_new_enclosures_validate_original_numeric_claims(self):
        d=json.loads((ROOT/'receipts.json').read_text(),parse_float=Decimal)
        for old,new in [('reg_interval','regulator'),('lead_coeff_interval','L_second_derivative_over_2')]:
            v=decode(self.record[new]);a,b=map(str,d[old])
            self.assertTrue(arb(a)<v and v<arb(b))

    def test_height_lower_bound_and_saturation_cutoff(self):
        self.assertEqual([p['x'] for p in self.record['exact']['small_height_candidates']],['-2','-1','0','1','3','4','6'])
        self.assertTrue(all(decode(v)>arb(1)/4 for v in self.record['heights'].values()))
        reg=decode(self.record['regulator'])
        self.assertTrue(0<reg<arb(3)/16)
        self.assertTrue(reg/3<arb(1)/16)

    def test_precision_and_tail_crosscheck(self):
        ctx.prec=1536
        hp,hq,hr=[height(x,64) for x in [0,1,-2]]
        reg=hp*hq-((hr-hp-hq)/2)**2
        self.assertTrue(reg.overlaps(decode(self.record['regulator'])))
        # Smaller Fourier/integration cutoffs require larger explicit tails.
        lead,tn,tt=leading_coefficient([0]+self.record['fourier_coefficients'][:128],128)
        self.assertTrue(lead.overlaps(decode(self.record['L_second_derivative_over_2'])))
        self.assertTrue(tn>decode(self.record['fourier_tail_bound']))
        ctx.prec=1024

    def test_torsion_counts_and_claim_boundary(self):
        self.assertEqual([finite_count(5),finite_count(7)],[9,13])
        self.assertFalse(self.record['formal_curve_theorem'])
        self.assertFalse(self.record['full_sha_triviality_proved'])

    def test_reversed_interval_rejected(self):
        with self.assertRaises(ValueError):interval(Q(2),Q(1))

if __name__=='__main__':unittest.main()
