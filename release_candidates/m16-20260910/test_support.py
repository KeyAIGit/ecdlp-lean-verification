# SPDX-License-Identifier: Apache-2.0
"""Regression tests for the public replay boundary, including failure cases."""
import unittest
from support import (determinant, divmod_poly, jacobian, mul, power_mod,
                     supported)
from replay import run


class SupportTests(unittest.TestCase):
    def test_exhaustive(self):
        result = run()
        self.assertEqual(result['polynomials_checked'], 5043)
        self.assertFalse(result['lean_checked'])
        self.assertEqual(result['new_target_secp256k1_solutions'], 0)

    def test_repeated_root(self):
        g = mul([-1, 1], [-1, 1], 5)
        self.assertTrue(supported(g, [-1, 1], 5))
        self.assertNotEqual(determinant(jacobian(g, [-1, 1], 5), 5), 0)

    def test_unsupported_root(self):
        self.assertFalse(supported([0, 1], [-1, 1], 5))

    def test_characteristic_guard(self):
        with self.assertRaises(ValueError):
            supported([0, 0, 0, 1], [-1, 1], 3)

    def test_composite_modulus(self):
        with self.assertRaises(ValueError):
            supported([1, 1], [1, 1], 9)

    def test_boolean_modulus(self):
        with self.assertRaises(ValueError):
            supported([1, 1], [1, 1], True)

    def test_nonmonic(self):
        with self.assertRaises(ValueError):
            supported([1, 2], [1, 1], 5)

    def test_constant_g(self):
        with self.assertRaises(ValueError):
            supported([1], [1, 1], 5)

    def test_malformed_coefficients(self):
        for bad in ([], [1, '2'], [1, 1.0], [False, 1]):
            with self.assertRaises(ValueError):
                supported(bad, [1, 1], 5)

    def test_zero_divisor(self):
        with self.assertRaises(ValueError):
            divmod_poly([1], [0], 5)

    def test_negative_exponent(self):
        with self.assertRaises(ValueError):
            power_mod([1], -1, [1, 1], 5)

    def test_jacobian_non_solution(self):
        with self.assertRaises(ValueError):
            jacobian([0, 1], [-1, 1], 5)

    def test_squarefree_assumption_matters(self):
        g = [-1, 1]
        f = mul(g, g, 5)
        self.assertTrue(supported(g, f, 5))
        self.assertEqual(determinant(jacobian(g, f, 5), 5), 0)

    def test_zero_f(self):
        self.assertTrue(supported([-1, 1], [0], 5))
        self.assertEqual(determinant(jacobian([-1, 1], [0], 5), 5), 0)

    def test_limited_prime_domain(self):
        with self.assertRaises(ValueError):
            supported([1, 1], [1, 1], 10007)

    def test_nonsquare_matrix(self):
        with self.assertRaises(ValueError):
            determinant([[1, 2]], 5)

    def test_repeatability(self):
        self.assertEqual(run(), run())


if __name__ == '__main__':
    unittest.main()
