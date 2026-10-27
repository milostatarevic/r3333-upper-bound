"""Fault-path tests for accepting native solver results, not mathematical tests."""
import hashlib
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import uniform_campaign as campaign


class WorkerTests(unittest.TestCase):
    def run_fixture(self, solver, body=None, corrupt=False):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root/'scratch').mkdir()
            if body is not None:
                executable = root/'fake-solver'
                executable.write_text('#!/bin/sh\n'+body+'\n')
                executable.chmod(0o700)
            else:
                executable = Path('/opt/homebrew/bin')/solver
            base = b'1 0\n'
            complete = b'p cnf 7320 2\n1 0\n-1 0\n'
            expected = {'bytes': len(complete), 'sha256': hashlib.sha256(complete).hexdigest(),
                        'variables': 7320, 'clauses': 2}
            if corrupt:
                expected['sha256'] = '0'*64
            rows = [{'id': 0, 'family': 'test', 'case_id': 'tiny', 'units': [-1], 'formula': expected}]
            campaign.STATE.update(root=root, rows=rows, base=base, solvers={solver: {
                'path': str(executable), 'binary': campaign.pin(executable), 'options': []}})
            result = campaign.run_one((0, solver))
            record = json.loads((root/result['result']).read_text())
            return result, record, (root/'runs'/solver/'00000/NATIVE_START.json').exists()

    def test_exact_status_and_exit_required(self):
        for exit_code, log in [(0, ''), (0, 's UNSATISFIABLE\n'), (20, ''),
                               (20, 's UNSATISFIABLE\ns SATISFIABLE\n'),
                               (-11, 's UNSATISFIABLE\n')]:
            self.assertEqual(campaign.classify(exit_code, log), 'ERROR')
        self.assertEqual(campaign.classify(20, 's UNSATISFIABLE\n'), 'UNSAT')
        self.assertEqual(campaign.classify(10, 's SATISFIABLE\n'), 'SAT')

    @unittest.skipUnless(os.environ.get('UNIFORM_NATIVE_SMOKE') == '1',
                         'Native solver smoke tests are opt-in; CI performs no SAT run')
    def test_native_tiny_unsat_both_solvers(self):
        for solver in ('kissat', 'cadical'):
            result, record, started = self.run_fixture(solver)
            self.assertEqual(result['status'], 'UNSAT', record)
            self.assertTrue(started)
            self.assertEqual(record['input_before'], record['input_after'])
            self.assertEqual(record['exit_code'], 20)
            self.assertGreaterEqual(record['native_CPU_seconds'], 0)

    def test_exit_zero_without_status(self):
        result, record, _ = self.run_fixture('fake', 'exit 0')
        self.assertEqual(result['status'], 'ERROR')
        self.assertEqual(record['exit_code'], 0)

    def test_signal_is_error(self):
        result, record, _ = self.run_fixture('fake', 'kill -TERM $$')
        self.assertEqual(result['status'], 'ERROR')
        self.assertEqual(record['exit_code'], -15)

    def test_input_corruption_prevents_launch(self):
        result, record, started = self.run_fixture('fake', 'exit 20', corrupt=True)
        self.assertEqual(result['status'], 'ERROR')
        self.assertFalse(started)
        self.assertIn('digest mismatch', record['error'])

    def test_missing_conflicts_not_invented_as_zero(self):
        result, record, _ = self.run_fixture('fake', 'echo "s UNSATISFIABLE"\nexit 20')
        self.assertEqual(result['status'], 'UNSAT')
        self.assertIsNone(record['conflicts'])
        self.assertFalse(record['conflicts_reported'])

    def test_failed_start_record_still_waits_for_child(self):
        original = campaign.write_record
        def broken(path, record):
            if Path(path).name == 'NATIVE_START.json':
                raise OSError('injected metadata failure')
            return original(path, record)
        with patch.object(campaign, 'write_record', broken):
            result, record, started = self.run_fixture('fake',
                '/bin/sleep 0.1\necho "s UNSATISFIABLE"\nexit 20')
        self.assertEqual(result['status'], 'ERROR')
        self.assertFalse(started)
        self.assertEqual(record['exit_code'], 20)
        self.assertGreaterEqual(record['native_wall_seconds'], 0.09)
        self.assertIn('injected metadata failure', record['error'])


if __name__ == '__main__':
    unittest.main()
