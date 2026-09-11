# SPDX-License-Identifier: Apache-2.0
import itertools
import json
import unittest
from pathlib import Path
import projection_check as pc

class ProjectionTests(unittest.TestCase):
    def test_zero_selector_rejected(self):
        with self.assertRaises(ValueError):pc.project([0,0,0],[0,0,0],5)
    def test_shape_rejected(self):
        with self.assertRaises(ValueError):pc.project([0,0],[1,0,0],5)
    def test_composite_modulus_rejected(self):
        with self.assertRaises(ValueError):pc.project([0,1,2],[1,0,0],9)
    def test_nonstrict_inputs_rejected(self):
        with self.assertRaises(ValueError):pc.project([0,True,2],[1,0,0],5)
        with self.assertRaises(ValueError):pc.project([0,1,2],[1,0,0],True)
    def test_projective_enumeration(self):
        for p in [3,5,7]:
            for m in [2,3,4]:
                vs=list(pc.projective_points(p,m))
                self.assertEqual(len(vs),sum(p**i for i in range(m)))
                self.assertEqual(len(vs),len(set(vs)))
    def test_every_original_zero_retained(self):
        for v in pc.projective_points(5,3):self.assertFalse(any(pc.project([0,0,0],v,5)))
    def test_scaling_does_not_change_zero_set(self):
        for v in pc.projective_points(3,3):
            for s in itertools.product(range(3),repeat=3):
                a=not any(pc.project(s,v,3))
                b=not any(pc.project(s,[2*x%3 for x in v],3))
                self.assertEqual(a,b)
    def test_full_probability_checks(self):
        for p in [3,5,7,11]:
            report=pc.linear_exhaustive(p)
            self.assertEqual(report['total_extra_zeros'],p*p-2)
    def test_norm_census_and_independent_oracle(self):
        root=Path(__file__).resolve().parent
        plan=json.loads((root/'PLAN.json').read_text())
        observed=pc.norm_census(plan)
        expected=json.loads((root/'RESULTS.json').read_text())['norm_census']
        self.assertEqual(observed,expected)
        self.assertTrue(observed['multiset_oracle_agrees'])

    def test_selected_projection_extra_roots(self):
        root=Path(__file__).resolve().parent
        plan=json.loads((root/'PLAN.json').read_text())
        selector=json.loads((root/'SYMBOLIC_PLAN.json').read_text())['selector']
        observed=pc.norm_census(plan,selector)['selected_projection']
        self.assertEqual(observed,json.loads((root/'SELECTED_PROJECTION.json').read_text()))
        self.assertTrue(observed['all_original_roots_retained'])

if __name__=='__main__':unittest.main()
