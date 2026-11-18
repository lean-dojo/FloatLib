"""Regression cases for the final signed-zero boundary of the finite MX oracle."""
from fractions import Fraction
import unittest

from mx_finite_dot import output_word


class FinalOutputTests(unittest.TestCase):
    def test_halfway_underflow_keeps_sign(self):
        for width, exponent in [(16, 25), (32, 150), (64, 1075)]:
            half_least = Fraction(1, 1 << exponent)
            self.assertEqual(output_word(half_least, width), 0)
            self.assertEqual(output_word(-half_least, width), 1 << (width - 1))

    def test_above_halfway_chooses_least_subnormal(self):
        for width, exponent in [(16, 25), (32, 150), (64, 1075)]:
            above_half = Fraction(3, 1 << (exponent + 1))
            self.assertEqual(output_word(above_half, width), 1)
            self.assertEqual(output_word(-above_half, width), (1 << (width - 1)) + 1)

    def test_exact_rational_zero_is_positive(self):
        for width in [16, 32, 64]:
            self.assertEqual(output_word(Fraction(0), width), 0)


if __name__ == "__main__":
    unittest.main()
