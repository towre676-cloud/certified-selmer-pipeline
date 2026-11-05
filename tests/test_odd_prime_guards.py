"""Guard tests do not import the heavy Sage runtime or certify p-adic data."""
from pathlib import Path
import sys
import unittest
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'arithmetic'))
from odd_primary_replay import run, irreducibility_witness

class OddPrimeGuardTests(unittest.TestCase):
    def test_unreviewed_primes_fail_before_backend_import(self):
        for p in [2,3,17,25,True]:
            with self.subTest(p=p):
                with self.assertRaises(ValueError):run((p,))

    def test_empty_or_duplicate_selection_rejected(self):
        for selected in [(),(5,5)]:
            with self.assertRaises(ValueError):run(selected)

    def test_irreducibility_witnesses_by_independent_square_enumeration(self):
        for p in [5,7,11,13]:
            w=irreducibility_witness(p)
            self.assertNotEqual(w['q'],p)
            d=(w['a_q']**2-4*w['q'])%p
            self.assertEqual(d,w['discriminant_mod_p'])
            self.assertNotIn(d,{r*r%p for r in range(p)})

if __name__=='__main__':unittest.main()
