"""Synthetic, non-certifying unit tests for the M11 20k-decimal acceptance gate."""
import unittest
from fractions import Fraction as Q
from m11_remaining_3600000_final_audit import (
    same_decimal_cell, exact_decimal, verify_length, verify_curvature,
)


def bounds(a, b):
    def rat(x):
        return {"numerator": str(x.numerator), "denominator": str(x.denominator)}
    return {"lower": rat(a), "upper": rat(b)}


class ExactCellTests(unittest.TestCase):
    def test_simple_nearest_even(self):
        self.assertEqual(same_decimal_cell(Q('1.2340'), Q('1.2341'), 2), 123)
        self.assertEqual(same_decimal_cell(Q('1.2361'), Q('1.2374'), 2), 124)

    def test_exact_boundary_rejected(self):
        for x in ('1.235', '1.245'):
            with self.subTest(x=x), self.assertRaises(ValueError):
                same_decimal_cell(Q(x), Q(x), 2)

    def test_crossing_boundary_rejected(self):
        with self.assertRaises(ValueError):
            same_decimal_cell(Q('1.234'), Q('1.236'), 2)

    def test_20000_places_and_serialization(self):
        places = 20_000
        k = int('203783759536049443826081' + '0' * (places - 24))
        scale = 10 ** places
        a, b = Q(k, scale) - Q(1, 4 * scale), Q(k, scale) + Q(1, 4 * scale)
        self.assertEqual(same_decimal_cell(a, b), k)
        s = exact_decimal(k)
        self.assertTrue(s.startswith('0.203783759536049443826081'))
        self.assertEqual(len(s.split('.')[1]), places)


class SumEnclosureTests(unittest.TestCase):
    def test_length_recomposition_and_missing_panel(self):
        n = 32
        m = {'panels': n, 'index': None, 'working_bits': 80000,
             'threshold_bits': 70000, 'enclosure': bounds(Q('5.55101'), Q('5.55103'))}
        ps = [{'panels': n, 'index': i, 'working_bits': 80000,
               'threshold_bits': 70000,
               'enclosure': bounds(Q('5.55102') / n, Q('5.55102') / n)} for i in range(n)]
        verify_length(m, ps)
        with self.assertRaises(ValueError):
            verify_length(m, ps[:-1])
        ps[10]['enclosure'] = bounds(Q('5.56') / n, Q('5.56') / n)
        with self.assertRaises(ValueError):
            verify_length(m, ps)

    def test_curvature_requires_sqrt_of_both_halves(self):
        n = 32
        z = Q('0.203783759536049443826081')
        half = z * z / 2
        m = {'quantity': 'D_kappa, Eq. (50)', 'parameters': {'bits': 80000, 'panels': n},
             'halves': [{'direction': d, 'orders': [3] * (n // 2),
                         'integral': bounds(half, half)} for d in (-1, 1)],
             'discrepancy': bounds(z, z)}
        verify_curvature(m)
        m['halves'][0]['integral'] = bounds(half + Q(1, 100), half + Q(1, 100))
        with self.assertRaises(ValueError):
            verify_curvature(m)


if __name__ == '__main__':
    unittest.main()
