"""Witness, boundary and allocation checks for the balanced encoding."""
import unittest

import uniform_balance as balance
import uniform_k61 as generator


class BalanceControls(unittest.TestCase):
    def test_all_ordered_anchors_and_disjoint_local_auxiliaries(self):
        matrices, states, patterns, reference = balance.tables(generator.template)
        self.assertEqual([len(patterns[kind]) for kind in ('U', 'T')], [16, 16])
        self.assertEqual(len(states), 6)
        for owner in balance.OWNERS:
            allocated = set()
            for side in range(2):
                for center in range(16):
                    anchor, first = balance.scope(owner, side, center, matrices, reference)
                    self.assertEqual(len(set(anchor)), 5)
                    interval = set(range(first, first+182))
                    self.assertTrue(allocated.isdisjoint(interval))
                    allocated |= interval
            self.assertEqual(allocated, set(range(7833, 13657)))
            self.assertTrue(allocated.isdisjoint(range(7321,7833)))


if __name__ == '__main__':
    unittest.main()
