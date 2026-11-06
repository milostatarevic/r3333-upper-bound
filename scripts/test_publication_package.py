"""Fail-closed controls for release authentication and completion claims."""
from copy import deepcopy
from decimal import Decimal, ROUND_HALF_UP
import hashlib
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import Mock, patch
from types import SimpleNamespace

import check_publication as package


class ReleaseControls(unittest.TestCase):
    def test_unsafe_members(self):
        for text in ('/absolute', '../escape', 'a/../../escape', 'a//b', 'a/./b',
                     'a\\b', '', '.', './file'):
            with self.subTest(text=text), self.assertRaises(ValueError):
                package.member(text)
        self.assertEqual(str(package.member('formal/src/A.lean')), 'formal/src/A.lean')

    def test_duplicate_keys(self):
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / 'x.json'
            path.write_text('{"cadical_complete": false, "cadical_complete": true}')
            with self.assertRaises(ValueError):
                package.read(path)

    def test_linked_payload_rejected(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary).resolve()
            (root / 'real').write_bytes(b'payload')
            (root / 'link').symlink_to(root / 'real')
            with self.assertRaises(ValueError):
                package.pin(root / 'link')

    def index(self, root, **changes):
        document = {'schema': package.SCHEMA, 'selected_formulas': 296081,
                    'balance_formulas': 7, 'production_campaign_inputs': 296797,
                    'kissat_complete': True, 'cadical_complete': False,
                    'publication_ready': False, 'status': 'PREPARED_PENDING_CADICAL'}
        document.update(changes)
        path = root / 'publication/checks/K60_RELEASE.json'
        path.parent.mkdir(parents=True, exist_ok=True)
        payload = json.dumps(document).encode(); path.write_bytes(payload)
        return hashlib.sha256(payload).hexdigest()

    def test_external_hash_authenticates_before_parsing(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary).resolve()
            self.index(root)
            with self.assertRaisesRegex(ValueError, 'hash mismatch'):
                package.check_index(root, '0' * 64)

    def test_pending_campaign_cannot_pass_publication_gate(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary).resolve(); digest = self.index(root)
            with self.assertRaisesRegex(ValueError, 'CaDiCaL evidence is still pending'):
                package.check_index(root, digest, require_cadical=True)

    def test_inconsistent_completion_and_case_claims(self):
        changes = ({'publication_ready': True}, {'status': 'READY_FOR_HUMAN_REVIEW'},
                   {'cadical_complete': 1}, {'selected_formulas': 296797},
                   {'balance_formulas': 723}, {'kissat_complete': False})
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary).resolve()
            for change in changes:
                digest = self.index(root, **change)
                with self.subTest(change=change), self.assertRaises(ValueError):
                    package.check_index(root, digest)


class ArchiveTransportControls(unittest.TestCase):
    # A small cap exercises the exact production chunking rules without
    # allocating multi-gigabyte test files.
    def setUp(self):
        self.cap = patch.object(package, 'MAX_ARCHIVE_PART_BYTES', 5)
        self.cap.start()
        self.addCleanup(self.cap.stop)

    def fixture(self, root, split=True):
        label = 'native' if split else 'formal'
        logical = 'archives/k60-' + label + '-evidence.tar.gz'
        payload = b'abcdefgh'
        whole = {'bytes': len(payload), 'sha256': hashlib.sha256(payload).hexdigest()}
        capsule = {'archive': logical, 'archive_pin': whole}
        catalogue = {'path': logical, 'archive': whole}
        files = {}
        (root / 'archives').mkdir()
        if split:
            parts = []
            for number, block in enumerate((payload[:5], payload[5:]), 1):
                name = logical + f'.part{number:02d}'
                (root / name).write_bytes(block)
                record = package.pin(root / name)
                parts.append({'path': name, **record})
                files[name] = record
            capsule['parts'] = parts
            catalogue['parts'] = deepcopy(parts)
        else:
            (root / logical).write_bytes(payload)
            files[logical] = whole
        return label, capsule, catalogue, files

    def check(self, root, fixture, **kwargs):
        return package.check_archive_transport(root, *fixture, **kwargs)

    def repin_part(self, root, fixture, number):
        _, capsule, catalogue, files = fixture
        part = capsule['parts'][number]
        record = package.pin(root / part['path'])
        part.update(record); catalogue['parts'][number].update(record)
        files[part['path']] = record

    def test_split_and_historical_unsplit_authenticate(self):
        for split in (False, True):
            with self.subTest(split=split), tempfile.TemporaryDirectory() as temporary:
                root = Path(temporary).resolve(); fixture = self.fixture(root, split)
                self.assertEqual(self.check(root, fixture), set(fixture[3]))
                self.assertEqual(self.check(root, fixture, archives=False), set(fixture[3]))

    def test_reordered_missing_duplicate_or_noncanonical_declarations_rejected(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary).resolve(); original = self.fixture(root)
            for change in ('reordered', 'missing', 'duplicate', 'gap', 'unsafe', 'empty', 'disagreement'):
                fixture = deepcopy(original); _, capsule, catalogue, _ = fixture
                if change == 'reordered': capsule['parts'].reverse()
                elif change == 'missing': capsule['parts'].pop()
                elif change == 'duplicate': capsule['parts'][1] = deepcopy(capsule['parts'][0])
                elif change == 'gap': capsule['parts'][1]['path'] = capsule['archive'] + '.part03'
                elif change == 'unsafe': capsule['parts'][0]['path'] = '../escape'
                elif change == 'empty': capsule['parts'] = []
                if change != 'disagreement': catalogue['parts'] = deepcopy(capsule['parts'])
                else: del catalogue['parts']
                for archives in (False, True):
                    with self.subTest(change=change, archives=archives), self.assertRaises(ValueError):
                        self.check(root, fixture, archives=archives)

    def test_invalid_part_sizes_hashes_and_inventory_rejected_even_when_skipped(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary).resolve(); original = self.fixture(root)
            mutations = [('bytes', 0), ('bytes', -1), ('bytes', True), ('bytes', 6),
                         ('bytes', 4), ('sha256', 'wrong'), ('path', original[1]['archive'])]
            for field, value in mutations:
                fixture = deepcopy(original); _, capsule, catalogue, files = fixture
                capsule['parts'][0][field] = value
                catalogue['parts'] = deepcopy(capsule['parts'])
                part = capsule['parts'][0]
                files[part['path']] = {key: part[key] for key in ('bytes', 'sha256')}
                with self.subTest(field=field, value=value), self.assertRaises(ValueError):
                    self.check(root, fixture, archives=False)
            for change in ('extra', 'logical', 'absent', 'pin', 'total'):
                fixture = deepcopy(original); _, capsule, catalogue, files = fixture
                if change == 'extra': files[capsule['archive'] + '.part03'] = deepcopy(files[capsule['parts'][1]['path']])
                elif change == 'logical': files[capsule['archive']] = capsule['archive_pin']
                elif change == 'absent': del files[capsule['parts'][0]['path']]
                elif change == 'pin': files[capsule['parts'][0]['path']] = {'bytes': 5, 'sha256': 'f' * 64}
                else:
                    capsule['archive_pin']['bytes'] += 1
                    catalogue['archive'] = deepcopy(capsule['archive_pin'])
                with self.subTest(change=change), self.assertRaises(ValueError):
                    self.check(root, fixture, archives=False)

    def test_numeric_type_coercion_in_catalogue_or_file_pins_rejected(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary).resolve(); original = self.fixture(root)
            for change in ('catalogue_archive', 'catalogue_part', 'file'):
                fixture = deepcopy(original); _, capsule, catalogue, files = fixture
                if change == 'catalogue_archive':
                    catalogue['archive'] = {**catalogue['archive'], 'bytes': 8.0}
                elif change == 'catalogue_part':
                    catalogue['parts'][0]['bytes'] = 5.0
                else:
                    files[capsule['parts'][0]['path']]['bytes'] = 5.0
                with self.subTest(change=change), self.assertRaises(ValueError):
                    self.check(root, fixture, archives=False)

    def test_missing_parts_are_skipped_only_when_requested(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary).resolve(); fixture = self.fixture(root)
            for path in fixture[3]: (root / path).unlink()
            self.assertEqual(self.check(root, fixture, archives=False), set(fixture[3]))
            with self.assertRaisesRegex(ValueError, 'regular archive part'):
                self.check(root, fixture)

    def test_corrupted_part_and_re_pinned_replacement_cannot_change_original_archive(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary).resolve(); fixture = self.fixture(root)
            (root / fixture[1]['parts'][0]['path']).write_bytes(b'xxxxx')
            with self.assertRaisesRegex(ValueError, 'Changed archive part'):
                self.check(root, fixture)
            self.repin_part(root, fixture, 0)
            self.check(root, fixture, archives=False)
            with self.assertRaisesRegex(ValueError, 'original logical archive'):
                self.check(root, fixture)

    def test_replaced_whole_hash_cannot_override_retained_bytes(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary).resolve(); fixture = self.fixture(root)
            fixture[1]['archive_pin']['sha256'] = 'f' * 64
            fixture[2]['archive'] = deepcopy(fixture[1]['archive_pin'])
            with self.assertRaisesRegex(ValueError, 'original logical archive'):
                self.check(root, fixture)

    def test_reordered_bytes_with_re_pinned_canonical_parts_rejected(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary).resolve(); fixture = self.fixture(root)
            # Keep lengths/names valid while moving the end before the beginning.
            (root / fixture[1]['parts'][0]['path']).write_bytes(b'fghab')
            (root / fixture[1]['parts'][1]['path']).write_bytes(b'cde')
            self.repin_part(root, fixture, 0); self.repin_part(root, fixture, 1)
            self.check(root, fixture, archives=False)
            with self.assertRaisesRegex(ValueError, 'original logical archive'):
                self.check(root, fixture)

    def test_linked_part_is_rejected(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary).resolve(); fixture = self.fixture(root)
            path = root / fixture[1]['parts'][0]['path']
            other = root / 'outside-part'; path.rename(other); path.symlink_to(other)
            with self.assertRaisesRegex(ValueError, 'regular archive part'):
                self.check(root, fixture)


class SuccessfulTimingControls(unittest.TestCase):
    def summary(self, cases, unsuccessful=0):
        successful_cpu = Decimal(cases * 2)
        excluded_cpu = Decimal(unsuccessful * 3)
        result = {'successful_runs': cases, 'unsuccessful_attempts': unsuccessful,
                'all_attempts': cases + unsuccessful,
                'successful_cpu_seconds': str(successful_cpu),
                'unsuccessful_cpu_seconds': str(excluded_cpu),
                'all_attempt_cpu_seconds': str(successful_cpu + excluded_cpu)}
        for prefix in ('successful', 'unsuccessful', 'all_attempt'):
            result[prefix + '_cpu_hours'] = format((Decimal(result[prefix + '_cpu_seconds']) / Decimal(3600)).quantize(
                Decimal('0.01'), rounding=ROUND_HALF_UP), 'f')
        return result

    def write_report(self, root, index, report):
        path = root / package.TIMINGS_REPORT
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(report))
        record = package.pin(path)
        index['files'][package.TIMINGS_REPORT] = record
        index['successful_run_timings']['report_pin'] = record

    def fixture(self, root):
        tool_path = 'reproduce/' + package.TIMINGS_TOOL
        tool = root / tool_path
        tool.parent.mkdir(parents=True, exist_ok=True)
        tool.write_text('# independently pinned timing calculator fixture\n')
        tool_pin = package.pin(tool)
        report = {'schema': package.TIMINGS_SCHEMA, 'selected_cases': package.TOTAL,
                  'native_manifest_sha256': 'a' * 64,
                  'selected_ordered_input_sha256': 'b' * 64,
                  'policy': 'One complete accepted UNSAT run per selected distinct formula.',
                  'timing_tool_sha256': tool_pin['sha256'], 'existing_all_attempt_fields_changed': False,
                  'solver_calls': 0,
                  'solvers': {name: self.summary(package.TOTAL, 1) for name in ('kissat', 'cadical')},
                  'families': []}
        for summary in report['solvers'].values():
            summary.update(selected_ordered_input_sha256='b' * 64, direct_c2_successful_runs=4,
                           successful_execution_census_sha256='c' * 64,
                           all_attempt_timing_census_sha256='d' * 64,
                           recorded_attempt_status_counts={'UNSAT': package.TOTAL, 'TIMEOUT': 1})
        counts = [package.TOTAL - 15] + [1] * 15
        for position, cases in enumerate(counts):
            report['families'].append({'family': 'family-' + str(position), 'cases': cases,
                                      **{name: self.summary(cases, int(position == 0))
                                         for name in ('kissat', 'cadical')}})
        index = {'files': {tool_path: tool_pin}, 'tools': {package.TIMINGS_TOOL: tool_pin},
                 'capsules': {'native': {'manifest_sha256': 'a' * 64}},
                 'selected_ordered_input_sha256': 'b' * 64,
                 'successful_run_timings': {'report': package.TIMINGS_REPORT, 'report_pin': None,
                     'tool': tool_path, 'tool_pin': tool_pin,
                     'native_manifest_sha256': 'a' * 64,
                     'selected_ordered_input_sha256': 'b' * 64}}
        self.write_report(root, index, report)
        return index, report

    def test_complete_timings_require_both_pinned_artifacts_and_binding(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary).resolve(); index, report = self.fixture(root)
            self.assertEqual(package.check_successful_run_timings(root, index), report)
            for mapping, key in [('files', package.TIMINGS_REPORT),
                                 ('files', 'reproduce/' + package.TIMINGS_TOOL),
                                 ('tools', package.TIMINGS_TOOL)]:
                altered = deepcopy(index); del altered[mapping][key]
                with self.subTest(mapping=mapping, key=key), self.assertRaisesRegex(ValueError, 'lacks'):
                    package.check_successful_run_timings(root, altered)
            altered = deepcopy(index); del altered['successful_run_timings']
            with self.assertRaisesRegex(ValueError, 'binding'):
                package.check_successful_run_timings(root, altered)
            (root / package.TIMINGS_REPORT).write_text('{}')
            with self.assertRaisesRegex(ValueError, 'Changed'):
                package.check_successful_run_timings(root, index)

    def test_wrong_capsule_census_policy_and_family_inventory_rejected(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary).resolve(); index, original = self.fixture(root)
            for field, value in [('native_manifest_sha256', 'c' * 64),
                                 ('selected_ordered_input_sha256', 'd' * 64),
                                 ('selected_cases', package.TOTAL - 1), ('selected_cases', float(package.TOTAL)),
                                 ('timing_tool_sha256', 'e' * 64), ('existing_all_attempt_fields_changed', True),
                                 ('solver_calls', True), ('policy', '')]:
                report = deepcopy(original); report[field] = value
                self.write_report(root, index, report)
                with self.subTest(field=field), self.assertRaises(ValueError):
                    package.check_successful_run_timings(root, index)
            for alteration in ('missing', 'duplicate', 'wrong_count'):
                report = deepcopy(original)
                if alteration == 'missing': report['families'].pop()
                elif alteration == 'duplicate': report['families'][1]['family'] = report['families'][0]['family']
                else: report['families'][0]['cases'] -= 1
                self.write_report(root, index, report)
                with self.subTest(alteration=alteration), self.assertRaisesRegex(ValueError, 'census'):
                    package.check_successful_run_timings(root, index)

    def test_unsuccessful_attempts_cannot_be_counted_as_completed_runs(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary).resolve(); index, original = self.fixture(root)
            for field, value in [('successful_runs', package.TOTAL + 1),
                                 ('unsuccessful_attempts', True), ('all_attempts', package.TOTAL),
                                 ('successful_cpu_seconds', 'NaN'), ('successful_cpu_seconds', '-1'),
                                 ('successful_cpu_seconds', 12), ('all_attempt_cpu_seconds', '592166'),
                                 ('successful_cpu_hours', '0.00'), ('direct_c2_successful_runs', 5),
                                 ('selected_ordered_input_sha256', 'e' * 64),
                                 ('recorded_attempt_status_counts', {'UNSAT': package.TOTAL + 1})]:
                report = deepcopy(original); report['solvers']['kissat'][field] = value
                self.write_report(root, index, report)
                with self.subTest(field=field, value=value), self.assertRaises(ValueError):
                    package.check_successful_run_timings(root, index)
            report = deepcopy(original)
            report['families'][0]['cadical']['successful_cpu_seconds'] = '0'
            report['families'][0]['cadical']['all_attempt_cpu_seconds'] = '3'
            report['families'][0]['cadical']['successful_cpu_hours'] = '0.00'
            report['families'][0]['cadical']['all_attempt_cpu_hours'] = '0.00'
            self.write_report(root, index, report)
            with self.assertRaisesRegex(ValueError, 'Family'):
                package.check_successful_run_timings(root, index)

    def test_recomputed_native_timings_defeat_self_consistent_repacked_totals(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary).resolve(); index, original = self.fixture(root)
            calculator = SimpleNamespace(__file__=str(root / 'reproduce' / package.TIMINGS_TOOL),
                                         derive=Mock(return_value=original))
            verified = {'passed': True, 'full_cadical_campaign_complete': True}
            native_root = root / 'native'
            with patch.dict('sys.modules', {'publication_timings': calculator}):
                self.assertEqual(package.recompute_successful_run_timings(root, index, native_root, verified), original)
                calculator.derive.assert_called_once_with(native_root, 'a' * 64, verified_result=verified)
                # Re-pin a mathematically consistent fabricated extra second in both
                # the family and grand totals. Only evidence recomputation catches it.
                altered = deepcopy(original)
                for summary in (altered['solvers']['cadical'], altered['families'][0]['cadical']):
                    for field in ('successful_cpu_seconds', 'all_attempt_cpu_seconds'):
                        summary[field] = str(Decimal(summary[field]) + 1)
                    for prefix in ('successful', 'all_attempt'):
                        summary[prefix + '_cpu_hours'] = format((Decimal(summary[prefix + '_cpu_seconds']) / Decimal(3600)).quantize(
                            Decimal('0.01'), rounding=ROUND_HALF_UP), 'f')
                self.write_report(root, index, altered)
                package.check_successful_run_timings(root, index)
                with self.assertRaisesRegex(ValueError, 'independently derived'):
                    package.recompute_successful_run_timings(root, index, native_root, verified)



if __name__ == '__main__':
    unittest.main()
