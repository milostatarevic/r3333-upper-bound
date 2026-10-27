"""Scope and input controls for the direct C entrance construction."""
from copy import deepcopy
from itertools import combinations
import unittest

import uniform_c
import uniform_k61


class CEntranceControls(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.rows = uniform_c.load()[0]['cases']
        cls.edges = list(combinations(range(61), 2))

    def decode(self, literal):
        return (*self.edges[(abs(literal)-1)//4], (abs(literal)-1) % 4, literal > 0)

    def test_complete_signed_neighborhood_and_untemplated_marked_cell(self):
        for case in self.rows:
            facts = [self.decode(lit) for lit in uniform_k61.c_units(case)]
            membership = {}
            for a, b, color, positive in facts:
                if b == 60 and color == 3:
                    membership[a] = positive
                if 47 <= a < b <= 60:
                    self.assertEqual((b, color, positive), (60, 3, False))
            self.assertEqual(set(membership), set(range(60)))
            expected = {0, *range(1, case['shape'][0]+1),
                        *(15+v for v in case['left_support']),
                        *(31+v for v in case['right_support'])}
            self.assertEqual({v for v, yes in membership.items() if yes}, expected)

    def test_cross_word_must_cover_exactly_selected_cross_edges(self):
        for replacement in ([0, 1, 0], [0, 40, 0], [0, 4, 3], [0, 4, True]):
            case = deepcopy(self.rows[0])
            case['word'][0] = replacement
            with self.subTest(replacement=replacement), self.assertRaises(ValueError):
                uniform_c.validate(case)
        case = deepcopy(self.rows[0])
        case['word'][0] = case['word'][1]
        with self.assertRaisesRegex(ValueError, 'coverage'):
            uniform_c.validate(case)

    def test_supports_and_case_identity_are_exact(self):
        for key, value in [('foreign', 'TU'), ('pair_index', True),
                           ('case_id', 'UU/455/pair_999/rep_000'),
                           ('left_support', [0, 1, 2, 3, 16]),
                           ('left_support', [0, 1, 2, 3, 3])]:
            case = deepcopy(self.rows[0]); case[key] = value
            with self.subTest(key=key, value=value), self.assertRaises(ValueError):
                uniform_c.validate(case)


if __name__ == '__main__':
    unittest.main()
