"""Small fault controls for retained second-solver evidence; no solver runs."""
import copy
import gzip
import io
import json
from pathlib import Path
import tarfile
import tempfile
import unittest
from unittest import mock

import abd_second_solver as target


def packed(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':')).encode()


def pin(path, raw):
    return {'path': path, 'bytes': len(raw), 'sha256': target.digest(raw)}


class Fixture:
    def __init__(self):
        self.counts = {'D_UUU': 1, 'D_UUT': 1}
        self.formulas, self.rows, self.logs = {}, [], {}
        for index, family in enumerate(self.counts):
            formula = {'case_id': 'shared/rep_000', 'bytes': 24 + index,
                       'sha256': str(index + 1) * 64, 'variables': 2 + index, 'clauses': 1}
            self.formulas[(family, formula['case_id'])] = copy.deepcopy(formula)
            log = ("c CaDiCaL SAT Solver\nc Version 3.0.1\n"
                   f"c found 'p cnf {2 + index} 1' header\ns UNSATISFIABLE\nc exit 20\n").encode()
            name = f'logs/{index:05d}.log'
            self.logs[name] = log
            identity = {key: formula[key] for key in ('bytes', 'sha256')}
            self.rows.append({'id': index, 'family': family, 'formula': formula,
                              'input_before': identity.copy(), 'input_after': identity.copy(),
                              'solver_sha256': target.SOLVER_SHA, 'status': 'UNSAT',
                              'exit_code': 20, 'raw_wait_status': 5120,
                              'native_CPU_seconds': 1.5, 'user_CPU_seconds': 1.4,
                              'system_CPU_seconds': .1, 'started_utc_epoch': 100.0,
                              'completed_utc_epoch': 102.0, 'peak_RSS_bytes': 4096,
                              'log': pin(name, log),
                              'source_sha256': {'native_result': 'a' * 64, 'native_start': 'b' * 64}})
        self.manifest = {'schema': 'RAMSEY_ABD_SECOND_SOLVER_1', 'cases': 2,
                         'family_counts': self.counts.copy(), 'solver': copy.deepcopy(target.SOLVER),
                         'native_CPU_seconds': 3.0, 'started_utc_epoch': 100.0,
                         'completed_utc_epoch': 102.0}
        self.summary = {'schema': 'RAMSEY_ABD_SECOND_SOLVER_SUMMARY_1', 'status': 'ALL_UNSAT',
                        'cases': 2, 'UNSAT': 2, 'SAT': 0, 'UNKNOWN': 0, 'errors': 0,
                        'solver': copy.deepcopy(target.SOLVER),
                        'families': {family: {'cases': 1, 'UNSAT': 1, 'native_CPU_seconds': 1.5}
                                     for family in self.counts},
                        'measurements': {'native_CPU_seconds': 3.0, 'worker_CPU_seconds': .1,
                                         'controller_CPU_seconds': .1, 'monitor_helper_CPU_seconds': .1,
                                         'raw_log_bytes': sum(map(len, self.logs.values())),
                                         'longest_solver_CPU_seconds': 1.5,
                                         'peak_single_solver_RSS_bytes': 4096,
                                         'started_utc': '1970-01-01T00:01:39+00:00',
                                         'finished_utc': '1970-01-01T00:01:42+00:00',
                                         'elapsed_seconds': 3.0}}

    def archive(self, entries_change=None, raw_records=None):
        records = raw_records if raw_records is not None else b''.join(packed(r) + b'\n' for r in self.rows)
        self.manifest['records'] = pin('results.jsonl', records)
        manifest = packed(self.manifest)
        summary = {**self.summary, 'manifest': pin('manifest.json', manifest),
                   'records': pin('results.jsonl', records)}
        entries = [('manifest.json', manifest, tarfile.REGTYPE), ('results.jsonl', records, tarfile.REGTYPE)]
        entries += [(name, raw, tarfile.REGTYPE) for name, raw in self.logs.items()]
        if entries_change:
            entries_change(entries)
        data = io.BytesIO()
        with tarfile.open(fileobj=data, mode='w', format=tarfile.USTAR_FORMAT) as archive:
            for name, raw, kind in entries:
                info = tarfile.TarInfo(name); info.type = kind; info.size = len(raw)
                if kind == tarfile.SYMTYPE:
                    info.linkname = '/elsewhere'
                archive.addfile(info, io.BytesIO(raw))
        raw = gzip.compress(data.getvalue(), mtime=0)
        summary['archive'] = pin('archives/abd-cadical.tar.gz', raw)
        return io.BytesIO(raw), summary

    def check(self, **kwargs):
        stream, summary = self.archive(**kwargs)
        return target.archive_check(stream, summary, self.formulas, self.counts)


class SecondSolverTests(unittest.TestCase):
    def test_complete_archive_passes_without_extraction(self):
        manifest, rows = Fixture().check()
        self.assertEqual(manifest['cases'], 2)
        self.assertEqual([row['family'] for row in rows], ['D_UUU', 'D_UUT'])

    def test_archive_must_match_pin_before_parsing(self):
        fixture = Fixture(); stream, summary = fixture.archive()
        summary['archive']['sha256'] = '0' * 64
        with self.assertRaisesRegex(ValueError, 'archive hash/size'):
            target.archive_check(stream, summary, fixture.formulas, fixture.counts)

    def test_incomplete_cover_rejected(self):
        fixture = Fixture(); fixture.rows.pop()
        with self.assertRaisesRegex(ValueError, 'case cover'):
            fixture.check()

    def test_duplicate_case_rejected(self):
        fixture = Fixture(); fixture.rows[1] = copy.deepcopy(fixture.rows[0]); fixture.rows[1]['id'] = 1
        with self.assertRaisesRegex(ValueError, 'formula owner'):
            fixture.check()

    def test_uut_uuu_owner_confusion_rejected(self):
        fixture = Fixture(); fixture.rows[0]['family'] = 'D_UUT'
        with self.assertRaisesRegex(ValueError, 'formula owner'):
            fixture.check()

    def test_each_formula_field_bound(self):
        for field, value in [('case_id', 'wrong'), ('sha256', '0' * 64), ('bytes', 99),
                             ('variables', 99), ('clauses', 99)]:
            fixture = Fixture(); fixture.rows[0]['formula'][field] = value
            with self.subTest(field=field), self.assertRaisesRegex(ValueError, 'formula owner'):
                fixture.check()

    def test_input_posthash_bound(self):
        fixture = Fixture(); fixture.rows[0]['input_after']['sha256'] = '0' * 64
        with self.assertRaisesRegex(ValueError, 'before/after'):
            fixture.check()

    def test_exit_status_and_solver_identity_bound(self):
        for field, value in [('exit_code', 0), ('exit_code', 10), ('raw_wait_status', 0),
                             ('status', 'SAT'), ('status', 'UNKNOWN'), ('solver_sha256', '0' * 64)]:
            fixture = Fixture(); fixture.rows[0][field] = value
            with self.subTest(field=field, value=value), self.assertRaises(ValueError):
                fixture.check()

    def test_cpu_failures(self):
        for field, value in [('native_CPU_seconds', -1), ('native_CPU_seconds', float('nan')),
                             ('native_CPU_seconds', float('inf')), ('user_CPU_seconds', -1),
                             ('system_CPU_seconds', .2), ('native_CPU_seconds', True)]:
            fixture = Fixture(); fixture.rows[0][field] = value
            with self.subTest(field=field, value=value), self.assertRaises(ValueError):
                fixture.check()

    def test_aggregate_cpu_bound(self):
        fixture = Fixture(); fixture.manifest['native_CPU_seconds'] = 4.0
        with self.assertRaisesRegex(ValueError, 'Aggregate native CPU'):
            fixture.check()

    def test_case_time_bound(self):
        for field, value in [('started_utc_epoch', 98), ('started_utc_epoch', 104),
                             ('completed_utc_epoch', 104), ('completed_utc_epoch', float('nan'))]:
            fixture = Fixture(); fixture.rows[0][field] = value
            with self.subTest(field=field), self.assertRaises(ValueError):
                fixture.check()

    def test_log_hash_bound(self):
        fixture = Fixture(); fixture.logs['logs/00000.log'] += b'c changed\n'
        with self.assertRaisesRegex(ValueError, 'member hash/size'):
            fixture.check()

    def test_log_status_version_dimensions_and_exit_bound(self):
        original = Fixture().logs['logs/00000.log']
        bad = [original.replace(b's UNSATISFIABLE', b's SATISFIABLE'),
               original.replace(b's UNSATISFIABLE', b's UNKNOWN'),
               original + b's UNSATISFIABLE\n',
               original.replace(b'3.0.1', b'3.0.0'),
               original.replace(b'p cnf 2 1', b'p cnf 3 1'),
               original.replace(b'c exit 20', b'c exit 0')]
        for raw in bad:
            fixture = Fixture(); fixture.logs['logs/00000.log'] = raw
            fixture.rows[0]['log'] = pin('logs/00000.log', raw)
            fixture.summary['measurements']['raw_log_bytes'] = sum(map(len, fixture.logs.values()))
            with self.subTest(raw=raw), self.assertRaises(ValueError):
                fixture.check()

    def test_tampered_summary_result_and_solver_rejected(self):
        for field, value in [('schema', 'other'), ('status', 'PARTIAL'), ('cases', 3), ('UNSAT', 1),
                             ('SAT', 1), ('UNKNOWN', 1), ('errors', 1), ('SAT', False)]:
            fixture = Fixture(); fixture.summary[field] = value
            with self.subTest(field=field), self.assertRaisesRegex(ValueError, 'Summary'):
                fixture.check()
        fixture = Fixture(); fixture.summary['solver']['version'] = '3.0.0'
        with self.assertRaisesRegex(ValueError, 'Summary solver'):
            fixture.check()

    def test_tampered_summary_family_rejected(self):
        for field, value in [('cases', 2), ('UNSAT', 0), ('native_CPU_seconds', 2.0),
                             ('native_CPU_seconds', float('nan'))]:
            fixture = Fixture(); fixture.summary['families']['D_UUU'][field] = value
            with self.subTest(field=field), self.assertRaises(ValueError):
                fixture.check()
        fixture = Fixture(); fixture.summary['families'].pop('D_UUU')
        with self.assertRaisesRegex(ValueError, 'Summary family census'):
            fixture.check()

    def test_tampered_summary_measurements_rejected(self):
        for field, value in [('native_CPU_seconds', 4.0), ('raw_log_bytes', 1),
                             ('longest_solver_CPU_seconds', 2.0), ('peak_single_solver_RSS_bytes', 5000),
                             ('elapsed_seconds', 4.0), ('elapsed_seconds', float('nan')),
                             ('worker_CPU_seconds', float('inf')), ('controller_CPU_seconds', -1),
                             ('monitor_helper_CPU_seconds', True)]:
            fixture = Fixture(); fixture.summary['measurements'][field] = value
            with self.subTest(field=field), self.assertRaises(ValueError):
                fixture.check()

    def test_tampered_summary_timestamps_rejected(self):
        for field, value in [('started_utc', '1970-01-01T00:01:41+00:00'),
                             ('finished_utc', '1970-01-01T00:01:43+00:00'),
                             ('finished_utc', '1970-01-01T00:01:42'),
                             ('finished_utc', '1970-01-01T00:01:42+01:00'),
                             ('finished_utc', 'not a timestamp')]:
            fixture = Fixture(); fixture.summary['measurements'][field] = value
            with self.subTest(field=field), self.assertRaises(ValueError):
                fixture.check()

    def test_duplicate_json_key_rejected(self):
        fixture = Fixture()
        records = b''.join(packed(row) + b'\n' for row in fixture.rows)
        records = records.replace(b'"exit_code":20', b'"exit_code":0,"exit_code":20', 1)
        with self.assertRaisesRegex(ValueError, 'Duplicate JSON key'):
            fixture.check(raw_records=records)

    def test_duplicate_and_unsafe_member_names_rejected(self):
        for name in ['../outside', '/absolute', 'logs/../outside', 'logs\\outside', 'manifest.json']:
            fixture = Fixture()
            def change(entries):
                entries[2] = (name, entries[2][1], tarfile.REGTYPE)
            with self.subTest(name=name), self.assertRaises(ValueError):
                fixture.check(entries_change=change)

    def test_nonregular_member_rejected(self):
        for kind in [tarfile.DIRTYPE, tarfile.SYMTYPE, tarfile.LNKTYPE, tarfile.FIFOTYPE]:
            fixture = Fixture()
            def change(entries):
                entries[2] = (entries[2][0], entries[2][1], kind)
            with self.subTest(kind=kind), self.assertRaises(ValueError):
                fixture.check(entries_change=change)

    def test_hidden_gnu_longname_extension_rejected(self):
        def change(entries):
            entries.insert(2, ('././@LongLink', b'logs/00000.log\0', tarfile.GNUTYPE_LONGNAME))
        with self.assertRaisesRegex(ValueError, 'extended archive member'):
            Fixture().check(entries_change=change)

    def test_invalid_header_not_treated_as_padding(self):
        fixture = Fixture(); stream, summary = fixture.archive()
        raw = gzip.compress(b'!' * 512 + gzip.decompress(stream.getvalue()), mtime=0)
        summary['archive'] = pin('archives/abd-cadical.tar.gz', raw)
        with self.assertRaisesRegex(ValueError, 'Malformed archive header'):
            target.archive_check(io.BytesIO(raw), summary, fixture.formulas, fixture.counts)

    def test_missing_log_rejected(self):
        with self.assertRaisesRegex(ValueError, 'Missing archive member'):
            Fixture().check(entries_change=lambda entries: entries.pop())

    def test_extra_log_rejected(self):
        with self.assertRaisesRegex(ValueError, 'Extra archive member'):
            Fixture().check(entries_change=lambda entries: entries.append(('extra', b'x', tarfile.REGTYPE)))

    def test_log_and_metadata_size_limits(self):
        with mock.patch.object(target, 'LOG_LIMIT', 1), self.assertRaises(ValueError):
            Fixture().check()
        with mock.patch.object(target, 'META_LIMIT', 1), self.assertRaises(ValueError):
            Fixture().check()

    def test_entire_expanded_stream_is_bounded(self):
        reader = target.LimitedReader(io.BytesIO(b'abcdef'), 5)
        self.assertEqual(reader.read(3), b'abc')
        with self.assertRaisesRegex(ValueError, 'Expanded archive exceeds limit'):
            reader.read(3)

    def test_source_hash_fields_are_exact(self):
        fixture = Fixture(); fixture.rows[0]['source_sha256']['wait4'] = 'a' * 64
        with self.assertRaisesRegex(ValueError, 'source hash census'):
            fixture.check()

    def test_held_file_detects_mutation(self):
        with tempfile.TemporaryDirectory() as folder:
            path = Path(folder).resolve() / 'archive'
            path.write_bytes(b'initial')
            with self.assertRaisesRegex(ValueError, 'changed while reading'):
                with target.held_file(path) as stream:
                    self.assertEqual(stream.read(), b'initial')
                    path.write_bytes(b'changed')

    def test_held_file_rejects_symlink(self):
        with tempfile.TemporaryDirectory() as folder:
            path = Path(folder).resolve() / 'archive'; path.write_bytes(b'initial')
            link = path.with_name('link'); link.symlink_to(path)
            with self.assertRaises(ValueError):
                with target.held_file(link):
                    pass


if __name__ == '__main__':
    unittest.main()
