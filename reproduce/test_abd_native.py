"""Synthetic negative controls; no solver, certificate checker or Lean is run."""
import copy
import hashlib
import json
from pathlib import Path
import tempfile
import unittest
import abd_native as target


class FixtureSnapshot:
    def __init__(self, files):
        self.files = {k: v if isinstance(v, bytes) else json.dumps(v).encode() for k, v in files.items()}
        self.sources = {'/historical/' + k: k for k in files}

    def pin(self, path):
        data = self.files[path]
        return {'path': path, 'bytes': len(data), 'sha256': target.digest(data)}

    def ref(self, path):
        return {**self.pin(path), 'path': '/historical/' + path}

    def read(self, path, expected=None):
        pin = self.pin(path)
        if expected is not None:
            target.need(expected['sha256'] == pin['sha256'] and expected.get('bytes', pin['bytes']) == pin['bytes'],
                        'Fixture reference mismatch')
        return self.files[path]

    def json(self, path, expected=None):
        return target.decode(self.read(path, expected))

    def reference(self, ref):
        path = self.sources[ref['path']]
        return path, self.json(path, ref)


def common_fixture(source='original'):
    cid = target.PILOT_CASE if source == 'pilot' else 'owner/case'
    job = target.PILOT_JOB if source == 'pilot' else 'SELECTED_A/' + cid
    formula = {'case_id': cid, 'sha256': 'a' * 64, 'bytes': 20, 'variables': 2, 'clauses': 1}
    args = {'job_id': job, 'cnf': '/historical/deleted.cnf', 'cnf_sha256': formula['sha256'],
            'cnf_bytes': 20, 'variables': 2, 'clauses': 1, 'solver_sha256': target.KISSAT_SHA}
    claim = {'job_id': job, 'arguments': args}
    stdout, stderr = b'c solver\ns UNSATISFIABLE\n', b''
    def pin(data):
        return {'bytes': len(data), 'sha256': target.digest(data)}
    result = {'schema': 'SHARED_NEIGHBORHOOD_NATIVE_PROBE_RESULT_1', 'status': 'UNSAT', 'job_id': job,
              'native': {'returncode': 20, 'raw_wait_status': 5120, 'signal': None,
                         'cpu_seconds': 1.5, 'user_cpu_seconds': 1.4, 'system_cpu_seconds': .1},
              'reaped': True, 'terminal': {'status_line': 'UNSATISFIABLE'}, 'received_signals': [], 'signals_sent': [],
              'claim': claim, 'input': {'path': args['cnf'], 'census': {k: v for k, v in formula.items() if k != 'case_id'}},
              'input_posthash': {k: formula[k] for k in ('sha256', 'bytes')},
              'input_transport': 'inherited read-only fd; /dev/fd path; original fd held until posthash',
              'solver': {'sha256': target.KISSAT_SHA, 'bytes': 392456},
              'solver_posthash': {'sha256': target.KISSAT_SHA, 'bytes': 392456},
              'logs': {'stdout.log': pin(stdout), 'stderr.log': pin(stderr)},
              'unsat_certificate_checked': False, 'kernel_credit': False}
    path = 'evidence/D/UUT/native_000/RESULT.json' if source == 'pilot' else 'jobs/one/RESULT.json'
    folder = str(Path(path).parent)
    files = {path: result, folder + '/CLAIM.json': copy.deepcopy(claim),
             folder + '/stdout.log': stdout, folder + '/stderr.log': stderr}
    return files, path, formula, {'source': source, 'summary_cpu': 1.5}


def run_common(files, path, formula, selection, family='A'):
    snapshot = FixtureSnapshot(files)
    return target.native_result(snapshot, family, formula, {**selection, 'ref': snapshot.ref(path)})


class NativeJoinTests(unittest.TestCase):
    def test_native_pass(self):
        row = run_common(*common_fixture())
        self.assertEqual((row['status'], row['exit_code']), ('UNSAT', 20))

    def test_uut_pilot_pass(self):
        row = run_common(*common_fixture('pilot'), family='D_UUT')
        self.assertEqual(row['source'], 'pilot')

    def test_wrong_family_cannot_use_pilot(self):
        with self.assertRaisesRegex(ValueError, 'pilot owner'):
            run_common(*common_fixture('pilot'))

    def test_status_and_exit_fail_closed(self):
        for field, value in [('status', 'SAT'), ('native.returncode', 0), ('native.raw_wait_status', 0),
                             ('native.signal', 9), ('reaped', False), ('signals_sent', ['SIGTERM'])]:
            files, path, formula, selected = common_fixture()
            node = files[path]; pieces = field.split('.')
            for piece in pieces[:-1]:
                node = node[piece]
            node[pieces[-1]] = value
            with self.subTest(field=field), self.assertRaises(ValueError):
                run_common(files, path, formula, selected)

    def test_each_native_input_dimension_is_bound(self):
        for field, value in [('sha256', 'b' * 64), ('bytes', 21), ('variables', 3), ('clauses', 2)]:
            files, path, formula, selected = common_fixture()
            files[path]['input']['census'][field] = value
            with self.subTest(field=field), self.assertRaisesRegex(ValueError, 'input hash/dimensions'):
                run_common(files, path, formula, selected)

    def test_posthash_is_bound(self):
        files, path, formula, selected = common_fixture()
        files[path]['input_posthash']['sha256'] = 'b' * 64
        with self.assertRaisesRegex(ValueError, 'posthash'):
            run_common(files, path, formula, selected)

    def test_case_owner_is_bound(self):
        files, path, formula, selected = common_fixture(); formula['case_id'] = 'different/case'
        with self.assertRaisesRegex(ValueError, 'case owner'):
            run_common(files, path, formula, selected)

    def test_separate_claim_is_bound(self):
        files, path, formula, selected = common_fixture()
        files[str(Path(path).parent) + '/CLAIM.json']['arguments']['clauses'] = 2
        with self.assertRaisesRegex(ValueError, 'claim mismatch'):
            run_common(files, path, formula, selected)

    def test_claim_formula_is_bound(self):
        files, path, formula, selected = common_fixture()
        files[path]['claim']['arguments']['cnf_sha256'] = 'b' * 64
        files[str(Path(path).parent) + '/CLAIM.json'] = copy.deepcopy(files[path]['claim'])
        with self.assertRaisesRegex(ValueError, 'Claim input'):
            run_common(files, path, formula, selected)

    def test_solver_identity_is_bound(self):
        files, path, formula, selected = common_fixture(); files[path]['solver']['sha256'] = 'b' * 64
        with self.assertRaisesRegex(ValueError, 'Solver identity'):
            run_common(files, path, formula, selected)

    def test_native_cpu_is_bound(self):
        files, path, formula, selected = common_fixture(); selected['summary_cpu'] = 4
        with self.assertRaisesRegex(ValueError, 'CPU accounting'):
            run_common(files, path, formula, selected)

    def test_cpu_nonfinite_is_rejected(self):
        files, path, formula, selected = common_fixture(); files[path]['native']['cpu_seconds'] = float('nan')
        with self.assertRaises(ValueError):
            run_common(files, path, formula, selected)

    def test_unsat_log_status_is_unique(self):
        for data in [b'', b's SATISFIABLE\n', b's UNSATISFIABLE\ns SATISFIABLE\n', b's UNSATISFIABLE\ns UNSATISFIABLE\n']:
            with self.subTest(data=data), self.assertRaisesRegex(ValueError, 'exactly one UNSAT'):
                target.unsat_log(data)

    def test_stdout_hash_is_checked(self):
        files, path, formula, selected = common_fixture(); files[str(Path(path).parent) + '/stdout.log'] += b'c changed\n'
        with self.assertRaisesRegex(ValueError, 'reference mismatch'):
            run_common(files, path, formula, selected)

    def test_nonempty_stderr_is_rejected(self):
        files, path, formula, selected = common_fixture(); data = b'error\n'
        files[str(Path(path).parent) + '/stderr.log'] = data
        files[path]['logs']['stderr.log'] = {'bytes': len(data), 'sha256': target.digest(data)}
        with self.assertRaisesRegex(ValueError, 'Nonempty native stderr'):
            run_common(files, path, formula, selected)

    def test_result_reference_is_checked(self):
        files, path, formula, selected = common_fixture(); snapshot = FixtureSnapshot(files)
        ref = snapshot.ref(path); ref['sha256'] = '0' * 64
        with self.assertRaisesRegex(ValueError, 'reference mismatch'):
            target.native_result(snapshot, 'A', formula, {**selected, 'ref': ref})

    def test_missing_and_extra_cases_are_rejected(self):
        for current in ({'a'}, {'a', 'b', 'x'}):
            with self.subTest(current=current), self.assertRaisesRegex(ValueError, 'case cover'):
                target.exact_cover({'a', 'b'}, current)

    def test_overlapping_predecessor_is_rejected(self):
        with self.assertRaisesRegex(ValueError, 'overlap'):
            target.exact_cover({'a', 'b'}, {'a', 'b'}, {'b'})

    def test_disjoint_continuation_passes(self):
        target.exact_cover({'a', 'b'}, {'b'}, {'a'})

    def test_duplicate_case_owner_is_rejected(self):
        with self.assertRaisesRegex(ValueError, 'Duplicate case'):
            target.indexed([{'case_id': 'a'}, {'case_id': 'a'}], 'fixture')

    def test_duplicate_json_key_is_rejected(self):
        with self.assertRaisesRegex(ValueError, 'Duplicate JSON key'):
            target.decode(b'{"status":"UNSAT","status":"SAT"}')

    def test_resource_red_summary_is_rejected(self):
        row = {'status': 'UNSAT', 'classification': 'UNSAT_EXECUTOR', 'runner_returncode': 0, 'resource_red': True}
        with self.assertRaisesRegex(ValueError, 'clean UNSAT'):
            target.executor_row(row)

    def test_snapshot_read_checks_manifest_pin(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp).resolve(); (root / 'record').write_bytes(b'actual')
            snap = object.__new__(target.Snapshot); snap.root = root
            snap.records = {'record': (6, target.digest(b'frozen'))}
            snap.read_count = snap.read_bytes = 0; snap.read_digest = hashlib.sha256()
            with self.assertRaisesRegex(ValueError, 'hash/size mismatch'):
                snap.read('record')

    def test_snapshot_reference_does_not_open_original_path(self):
        snap = object.__new__(target.Snapshot); snap.sources = {}
        with self.assertRaisesRegex(ValueError, 'source missing'):
            snap.reference({'path': '/etc/passwd', 'sha256': '0' * 64})

    def test_uut_pilot_requires_matching_manifest_owner(self):
        path = 'evidence/D/UUT/full_native_000/RESULT.json'
        term = {'status': 'ALL_EXECUTOR_UNSAT_PENDING_REVIEW', 'error': None, 'never_launched_case_ids': [],
                'unrecorded_case_ids': [], 'unreconciled_attempt': None, 'received_signals': [], 'signals_sent': [],
                'recorded_results': [{'case_id': target.PILOT_CASE, 'status': 'UNSAT', 'source': 'accepted matched pilot',
                                     'result': '/historical/pilot', 'sha256': 'a' * 64, 'cpu_seconds': 1.5}]}
        with self.assertRaisesRegex(ValueError, 'pilot owner'):
            target.family_results(FixtureSnapshot({path: term}), 'D_UUT',
                                  {target.PILOT_CASE: {'pilot_input_matches_accepted': False}})

    def test_uuu_start_and_dimensions_are_bound(self):
        formula = {'case_id': 'f/c', 'sha256': 'a' * 64, 'bytes': 20, 'variables': 2, 'clauses': 1}
        path = 'evidence/D/UUU/results/f/c/RESULT.json'; folder = str(Path(path).parent)
        result = {'status': 'UNSAT', 'case_id': 'f/c', 'solver_exit_code': 20, 'phase': 'complete',
                  'kissat': {'s_line': 'UNSATISFIABLE'}, 'kissat_sha256': target.KISSAT_SHA, 'kissat_version': '4.0.4',
                  'materialize': {'dense_sha256': 'a' * 64, 'dense_bytes': 20, 'dense_header': [2, 1]},
                  'command': ['kissat', 'deleted.cnf'], 'bytes': {'solver_log': 16},
                  'timing': {'cpu_user_seconds': 1, 'cpu_sys_seconds': .1}}
        start = {'case_id': 'f/c', 'dense_sha256': 'a' * 64, 'kissat_sha256': target.KISSAT_SHA,
                 'command': ['kissat', 'deleted.cnf']}
        files = {path: result, folder + '/START.json': start, folder + '/kissat.log': b's UNSATISFIABLE\n'}
        snapshot = FixtureSnapshot(files)
        row = target.native_result(snapshot, 'D_UUU', formula, {'ref': snapshot.ref(path), 'source': 'original'})
        self.assertEqual(row['status'], 'UNSAT')
        for change in ('start', 'header'):
            altered = copy.deepcopy(files)
            if change == 'start':
                altered[folder + '/START.json']['dense_sha256'] = 'b' * 64
            else:
                altered[path]['materialize']['dense_header'] = [2, 2]
            snapshot = FixtureSnapshot(altered)
            with self.subTest(change=change), self.assertRaises(ValueError):
                target.native_result(snapshot, 'D_UUU', formula, {'ref': snapshot.ref(path), 'source': 'original'})


if __name__ == '__main__':
    unittest.main(verbosity=2)
