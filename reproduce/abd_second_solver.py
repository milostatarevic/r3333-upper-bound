#!/usr/bin/env python3
"""Check the retained CaDiCaL replay against every exact original A/B/D formula.

Authenticates and streams the supplemental archive without extracting it. This
checks recorded native UNSAT evidence; it does not execute a solver, validate a
refutation certificate, or replace the original Kissat joins in abd_native.py.
"""
import argparse
import collections
import contextlib
import datetime
import gzip
import json
import math
import os
from pathlib import Path, PurePosixPath
import re
import resource
import sys
import tarfile
import time

import abd_inputs
import abd_native
import verify

REPOSITORY = Path(__file__).resolve().parents[1]
SUMMARY = REPOSITORY / 'publication/checks/ABD_SECOND_SOLVER.json'
ARCHIVE = REPOSITORY / 'archives/abd-cadical.tar.gz'
SOLVER_SHA = '601c9fa8ba5d09fd81bb00c89b3e54832f138bccc3422bd8652e8cda4d74d1fa'
SOLVER = {'name': 'CaDiCaL', 'version': '3.0.1', 'bytes': 1250184,
          'sha256': SOLVER_SHA, 'arguments': ['--seed=0', '/dev/fd/4'],
          'proof_logging': False}
FAMILY_COUNTS = {name: record[1] for name, record in abd_inputs.MANIFESTS.items()}
COUNT = sum(FAMILY_COUNTS.values())
META_LIMIT = 64 << 20
LOG_LIMIT = 64 << 20
TOTAL_LIMIT = 4 << 30
ROW_KEYS = {'id', 'family', 'formula', 'input_before', 'input_after',
            'solver_sha256', 'status', 'exit_code', 'raw_wait_status',
            'native_CPU_seconds', 'user_CPU_seconds', 'system_CPU_seconds',
            'started_utc_epoch', 'completed_utc_epoch', 'peak_RSS_bytes',
            'log', 'source_sha256'}

need = abd_native.need
decode = abd_native.decode
digest = abd_native.digest


def number(value, label):
    need(type(value) in (int, float) and math.isfinite(value) and value >= 0,
         'Invalid nonnegative finite number: ' + label)
    return value


def same_number(left, right, label):
    number(left, label); number(right, label)
    need(math.isclose(left, right, rel_tol=1e-12, abs_tol=1e-6), label + ' mismatch')


def hash_value(value):
    need(isinstance(value, str) and re.fullmatch('[0-9a-f]{64}', value) is not None,
         'Invalid SHA256')


def pin(record, path, maximum):
    need(isinstance(record, dict) and set(record) == {'path', 'bytes', 'sha256'},
         'Invalid file pin')
    need(record['path'] == path and type(record['bytes']) is int and
         0 <= record['bytes'] <= maximum, 'Invalid pinned path/size: ' + path)
    hash_value(record['sha256'])


@contextlib.contextmanager
def held_file(path):
    path = verify.ordinary_path(path)
    before = path.stat()
    fd = os.open(path, os.O_RDONLY | getattr(os, 'O_NOFOLLOW', 0))
    with os.fdopen(fd, 'rb') as stream:
        need(verify.identity(before) == verify.identity(os.fstat(stream.fileno())),
             'File changed while opening')
        yield stream
        need(verify.identity(before) == verify.identity(os.fstat(stream.fileno())) ==
             verify.identity(path.stat()), 'File changed while reading')


class LimitedReader:
    """Bound the entire expanded tar, including padding and extension headers."""
    def __init__(self, source, maximum):
        self.source, self.maximum, self.size = source, maximum, 0

    def read(self, size=-1):
        remaining = self.maximum - self.size
        requested = remaining + 1 if size < 0 else min(size, remaining + 1)
        data = self.source.read(requested)
        self.size += len(data)
        need(self.size <= self.maximum, 'Expanded archive exceeds limit')
        return data


class StrictTarInfo(tarfile.TarInfo):
    @classmethod
    def fromtarfile(cls, archive):
        # Python 3.14's accelerated implementation bypasses frombuf. Keep this
        # small stdlib header-reading path explicit so every version applies
        # the checks below before processing GNU/PAX extension metadata.
        raw = archive.fileobj.read(tarfile.BLOCKSIZE)
        member = cls.frombuf(raw, archive.encoding, archive.errors)
        member.offset = archive.fileobj.tell() - tarfile.BLOCKSIZE
        return member._proc_member(archive)

    @classmethod
    def frombuf(cls, buf, encoding, errors):
        try:
            member = super().frombuf(buf, encoding, errors)
        except (tarfile.InvalidHeaderError, tarfile.TruncatedHeaderError) as error:
            # ignore_zeros permits standard trailing zero blocks, but must not
            # silently skip malformed headers. Reject extensions before tarfile
            # can normalize GNU/PAX headers into otherwise ordinary members.
            raise ValueError('Malformed archive header') from error
        need(member.type == tarfile.REGTYPE, 'Nonregular or extended archive member')
        return member


class Members:
    def __init__(self, archive):
        self.archive, self.seen, self.total = archive, set(), 0

    def read(self, expected, maximum, expected_pin=None):
        member = self.archive.next()
        need(member is not None, 'Missing archive member: ' + expected)
        name = member.name
        rel = PurePosixPath(name)
        need(not rel.is_absolute() and '..' not in rel.parts and str(rel) == name
             and '\\' not in name and name not in self.seen, 'Unsafe/duplicate archive member')
        need(member.type == tarfile.REGTYPE and not member.pax_headers and
             not member.issparse() and not member.linkname,
             'Nonregular or extended archive member')
        need(name == expected, 'Unexpected archive member: ' + name)
        need(type(member.size) is int and 0 <= member.size <= maximum,
             'Archive member exceeds limit')
        self.seen.add(name); self.total += member.size
        need(self.total <= TOTAL_LIMIT, 'Archive payload exceeds limit')
        stream = self.archive.extractfile(member)
        need(stream is not None, 'Unreadable archive member')
        with stream:
            raw = stream.read(maximum + 1)
        need(len(raw) == member.size, 'Truncated archive member')
        if expected_pin is not None:
            pin(expected_pin, name, maximum)
            need(len(raw) == expected_pin['bytes'] and digest(raw) == expected_pin['sha256'],
                 'Archive member hash/size mismatch: ' + name)
        return raw

    def finish(self):
        need(self.archive.next() is None, 'Extra archive member')


def manifest_check(manifest, summary, counts):
    need(manifest['schema'] == 'RAMSEY_ABD_SECOND_SOLVER_1', 'Unknown manifest schema')
    need(type(manifest['cases']) is int and manifest['cases'] == sum(counts.values())
         and manifest['family_counts'] == counts and
         all(type(n) is int for n in manifest['family_counts'].values()),
         'Manifest case census mismatch')
    need(manifest['solver'] == SOLVER and manifest['solver']['proof_logging'] is False,
         'Solver identity/arguments mismatch')
    pin(manifest['records'], 'results.jsonl', META_LIMIT)
    need(manifest['records'] == summary['records'], 'Records pin disagreement')
    number(manifest['native_CPU_seconds'], 'manifest CPU')
    started = number(manifest['started_utc_epoch'], 'manifest start')
    completed = number(manifest['completed_utc_epoch'], 'manifest completion')
    need(started <= completed, 'Manifest times reversed')


def records_check(raw, formulas, manifest, counts):
    rows, seen, families, cpu = [], set(), collections.Counter(), []
    for line in raw.splitlines():
        need(line and len(line) <= (1 << 20), 'Invalid result row size')
        row = decode(line)
        need(isinstance(row, dict) and set(row) == ROW_KEYS, 'Unexpected result row schema')
        need(type(row['id']) is int and row['id'] == len(rows), 'Duplicate/out-of-order case id')
        family, formula = row['family'], row['formula']
        need(isinstance(family, str) and isinstance(formula, dict) and
             set(formula) == {'case_id', 'bytes', 'sha256', 'variables', 'clauses'},
             'Invalid formula record')
        need(isinstance(formula['case_id'], str) and
             all(type(formula[k]) is int and formula[k] > 0 for k in ('bytes', 'variables', 'clauses')),
             'Invalid formula dimensions')
        hash_value(formula['sha256'])
        key = (family, formula['case_id'])
        need(key not in seen and key in formulas and formulas[key] == formula,
             'Duplicate, unknown, or mismatched formula owner')
        seen.add(key); families[family] += 1
        expected = {k: formula[k] for k in ('bytes', 'sha256')}
        need(row['input_before'] == row['input_after'] == expected, 'Input before/after mismatch')
        need(row['solver_sha256'] == SOLVER_SHA, 'Per-case solver identity mismatch')
        need(row['status'] == 'UNSAT' and type(row['exit_code']) is int and row['exit_code'] == 20
             and type(row['raw_wait_status']) is int and row['raw_wait_status'] == 5120,
             'Result is not clean exit20 UNSAT')
        total = number(row['native_CPU_seconds'], 'native CPU')
        user = number(row['user_CPU_seconds'], 'user CPU')
        system = number(row['system_CPU_seconds'], 'system CPU')
        same_number(total, user + system, 'Native CPU accounting')
        cpu.append(total)
        started = number(row['started_utc_epoch'], 'case start')
        completed = number(row['completed_utc_epoch'], 'case completion')
        need(manifest['started_utc_epoch'] <= started <= completed <= manifest['completed_utc_epoch'],
             'Case times outside campaign interval')
        need(type(row['peak_RSS_bytes']) is int and row['peak_RSS_bytes'] >= 0, 'Invalid peak RSS')
        pin(row['log'], f'logs/{row["id"]:05d}.log', LOG_LIMIT)
        need(isinstance(row['source_sha256'], dict) and
             set(row['source_sha256']) == {'native_result', 'native_start'}, 'Invalid source hash census')
        for value in row['source_sha256'].values():
            hash_value(value)
        rows.append(row)
    need(seen == set(formulas) and dict(families) == counts and len(rows) == manifest['cases'],
         'Incomplete or extra second-solver case cover')
    same_number(math.fsum(cpu), manifest['native_CPU_seconds'], 'Aggregate native CPU')
    return rows


def utc_epoch(value, label):
    need(isinstance(value, str), 'Invalid UTC timestamp: ' + label)
    parsed = datetime.datetime.fromisoformat(value)
    need(parsed.tzinfo is not None and parsed.utcoffset() == datetime.timedelta(0),
         'Timestamp must specify UTC: ' + label)
    return number(parsed.timestamp(), label)


def summary_check(summary, manifest, rows, counts):
    need(summary['schema'] == 'RAMSEY_ABD_SECOND_SOLVER_SUMMARY_1' and
         summary['status'] == 'ALL_UNSAT', 'Summary schema/status mismatch')
    expected = {'cases': sum(counts.values()), 'UNSAT': sum(counts.values()),
                'SAT': 0, 'UNKNOWN': 0, 'errors': 0}
    need(all(type(summary[k]) is int and summary[k] == value for k, value in expected.items()),
         'Summary result census mismatch')
    need(summary['solver'] == SOLVER and summary['solver']['proof_logging'] is False,
         'Summary solver identity mismatch')
    need(isinstance(summary['families'], dict) and set(summary['families']) == set(counts),
         'Summary family census mismatch')
    for family, count in counts.items():
        recorded = summary['families'][family]
        need(all(type(recorded[k]) is int and recorded[k] == count for k in ('cases', 'UNSAT')),
             'Summary family result census mismatch')
        cpu = math.fsum(row['native_CPU_seconds'] for row in rows if row['family'] == family)
        same_number(recorded['native_CPU_seconds'], cpu, 'Summary family CPU')
    measurements = summary['measurements']
    total_cpu = math.fsum(row['native_CPU_seconds'] for row in rows)
    same_number(measurements['native_CPU_seconds'], total_cpu, 'Summary native CPU')
    same_number(measurements['native_CPU_seconds'], manifest['native_CPU_seconds'],
                'Summary/manifest native CPU')
    same_number(measurements['longest_solver_CPU_seconds'],
                max(row['native_CPU_seconds'] for row in rows), 'Summary longest solver CPU')
    for key, expected_value in (
            ('raw_log_bytes', sum(row['log']['bytes'] for row in rows)),
            ('peak_single_solver_RSS_bytes', max(row['peak_RSS_bytes'] for row in rows))):
        need(type(measurements[key]) is int and measurements[key] == expected_value,
             'Summary ' + key + ' mismatch')
    started = utc_epoch(measurements['started_utc'], 'summary start')
    finished = utc_epoch(measurements['finished_utc'], 'summary finish')
    first_native = min(row['started_utc_epoch'] for row in rows)
    last_native = max(row['completed_utc_epoch'] for row in rows)
    need(started <= first_native and abs(finished - last_native) <= 1e-6 and
         abs(manifest['started_utc_epoch'] - first_native) <= 1e-6 and
         abs(manifest['completed_utc_epoch'] - last_native) <= 1e-6,
         'Summary/manifest execution interval mismatch')
    same_number(measurements['elapsed_seconds'], finished - started, 'Summary elapsed time')
    # These three source measurements are retained as reported; the compact
    # native archive contains no independent per-worker/controller accounting.
    for key in ('worker_CPU_seconds', 'controller_CPU_seconds', 'monitor_helper_CPU_seconds'):
        number(measurements[key], 'reported ' + key)


def log_check(raw, formula):
    statuses, versions, headers, exits = [], [], [], []
    banner = False
    for line in raw.decode('utf-8').splitlines():
        line = line.strip()
        if line.startswith('s '):
            statuses.append(line)
        if line == 'c CaDiCaL SAT Solver':
            banner = True
        if line.startswith('c Version '):
            versions.append(line[len('c Version '):])
        match = re.fullmatch(r"c found 'p cnf (\d+) (\d+)' header", line)
        if match:
            headers.append([int(match[1]), int(match[2])])
        if line.startswith('c exit '):
            exits.append(line)
    need(statuses == ['s UNSATISFIABLE'], 'Log does not have exactly one UNSAT status')
    need(banner and versions == ['3.0.1'], 'Log solver/version mismatch')
    need(headers == [[formula['variables'], formula['clauses']]], 'Log parsed header mismatch')
    need(exits == ['c exit 20'], 'Log terminal exit mismatch')


def archive_check(stream, summary, formulas, counts):
    pin(summary['archive'], 'archives/abd-cadical.tar.gz', TOTAL_LIMIT)
    pin(summary['manifest'], 'manifest.json', META_LIMIT)
    pin(summary['records'], 'results.jsonl', META_LIMIT)
    actual = verify.hash_stream(stream)
    need(actual == (summary['archive']['bytes'], summary['archive']['sha256']),
         'Supplemental archive hash/size mismatch')
    stream.seek(0)
    with gzip.GzipFile(fileobj=stream, mode='rb') as expanded:
        bounded = LimitedReader(expanded, TOTAL_LIMIT)
        with tarfile.open(fileobj=bounded, mode='r|', ignore_zeros=True,
                          tarinfo=StrictTarInfo) as archive:
            members = Members(archive)
            manifest = decode(members.read('manifest.json', META_LIMIT, summary['manifest']))
            manifest_check(manifest, summary, counts)
            rows = records_check(members.read('results.jsonl', META_LIMIT, summary['records']),
                                 formulas, manifest, counts)
            summary_check(summary, manifest, rows, counts)
            for row in rows:
                raw = members.read(row['log']['path'], LOG_LIMIT, row['log'])
                log_check(raw, row['formula'])
            members.finish()
    return manifest, rows


def reconstruct(snapshot):
    # The original manifest index authenticates the snapshot's identities; each
    # reconstruction also checks its pinned formula manifest and consumed assets.
    authenticated = abd_native.Snapshot(snapshot)
    formulas = {}
    for family in FAMILY_COUNTS:
        source = abd_inputs.Family(authenticated.root, family)
        for case in source.cases:
            _, formula = source.formula(case)
            key = (family, formula['case_id'])
            need(key not in formulas, 'Duplicate reconstructed formula owner')
            formulas[key] = formula
        del source
    need(len(formulas) == COUNT, 'Original formula census mismatch')
    return formulas


def run(snapshot, archive=ARCHIVE):
    start, wall = time.process_time(), time.monotonic()
    with held_file(SUMMARY) as source:
        raw = source.read(META_LIMIT + 1)
        need(len(raw) <= META_LIMIT, 'Summary exceeds limit')
        summary = decode(raw)
    formulas = reconstruct(snapshot)
    with held_file(archive) as stream:
        manifest, rows = archive_check(stream, summary, formulas, FAMILY_COUNTS)
    families = []
    for family, count in FAMILY_COUNTS.items():
        families.append({'family': family, 'formulas': count, 'native_UNSAT': count,
                         'native_CPU_seconds': math.fsum(row['native_CPU_seconds'] for row in rows
                                                       if row['family'] == family)})
    sources = []
    for path in (Path(__file__), Path(abd_inputs.__file__), Path(abd_native.__file__), Path(verify.__file__)):
        with held_file(path) as source:
            raw = source.read(META_LIMIT + 1)
            need(len(raw) <= META_LIMIT, 'Checker source exceeds limit')
        sources.append({'path': 'reproduce/' + path.name, 'bytes': len(raw), 'sha256': digest(raw)})
    return {'schema': 'RAMSEY61_PORTABLE_ABD_SECOND_SOLVER_JOIN_1',
            'status': 'PASS_ALL_56374_CADICAL_UNSAT_JOINS',
            'created_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
            'formulas': COUNT, 'native_UNSAT': COUNT, 'families': families,
            'solver': SOLVER, 'native_CPU_seconds': manifest['native_CPU_seconds'],
            'archive': summary['archive'], 'manifest': summary['manifest'], 'records': summary['records'],
            'original_archive_manifest_index_sha256': verify.INDEX_PIN[1],
            'source_files': sources,
            'CPU_seconds': time.process_time() - start, 'elapsed_seconds': time.monotonic() - wall,
            'peak_RSS_bytes': resource.getrusage(resource.RUSAGE_SELF).ru_maxrss *
                              (1 if sys.platform == 'darwin' else 1024),
            'solver_calls': 0, 'certificate_replays': 0, 'Lean_calls': 0,
            'complete_case_CNFs_written': 0, 'archive_members_extracted': 0,
            'scope': 'Every original A/B/D formula reconstructed and matched by family, case, '
                     'complete SHA256, byte size and dimensions to a retained CaDiCaL result. '
                     'Every raw log authenticated and checked for matching version, parsed header, '
                     'one UNSAT status and exit20. This checks recorded native evidence, not solver '
                     'correctness, refutation certificates, the original Kissat custody joins or mathematical coverage.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--snapshot', required=True, type=Path)
    parser.add_argument('--archive', default=ARCHIVE, type=Path)
    parser.add_argument('--receipt', type=Path)
    args = parser.parse_args()
    result = run(args.snapshot, args.archive)
    raw = (json.dumps(result, indent=2, sort_keys=True) + '\n').encode()
    if args.receipt:
        abd_inputs.exclusive_output(args.snapshot.resolve(strict=True), args.receipt, (raw,))
    print(raw.decode(), end='')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, OSError, KeyError, IndexError, TypeError, UnicodeError,
            EOFError, tarfile.TarError) as error:
        print('FAIL: ' + str(error), file=sys.stderr)
        sys.exit(1)
