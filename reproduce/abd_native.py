#!/usr/bin/env python3
"""Reconstruct all 56,374 A/B/D formulas and join their native UNSAT evidence.

Reads only an extracted evidence-v1 snapshot. Authenticating the pinned index,
its shards and each consumed record does not replace verify.py full's complete
archive census. Historical absolute paths are opaque source-map keys, never
filesystem inputs. No solver, certificate checker or Lean process is invoked.
"""
import argparse
import collections
import datetime
import hashlib
import json
import math
from pathlib import Path, PurePosixPath
import resource
import sys
import time

import abd_inputs
import verify

KISSAT_SHA = '05d6f3e9c402a1fe8853b0746e384e1b3d1c4a550e255f11daa2461d279aa848'
PILOT_CASE = 'D9_TWISTED_ROOT12/rep_009'
PILOT_JOB = 'ORIGINAL_UUT_D9_TWISTED_ROOT12_rep_009_000'


def need(ok, message):
    if not ok:
        raise ValueError(message)


def unique(pairs):
    out = {}
    for key, value in pairs:
        need(key not in out, 'Duplicate JSON key: ' + key)
        out[key] = value
    return out


def decode(data):
    return json.loads(data, object_pairs_hook=unique)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def indexed(rows, label):
    result = {}
    for row in rows:
        cid = row['case_id']
        need(isinstance(cid, str) and cid not in result, 'Duplicate case in ' + label)
        result[cid] = row
    return result


def exact_cover(required, current, inherited=()):
    a, b = set(current), set(inherited)
    need(not a & b, 'Current/inherited case overlap')
    need(a | b == set(required), 'Incomplete or extra native case cover')


class Snapshot:
    def __init__(self, root):
        self.root = root.resolve(strict=True)
        need(self.root.is_dir(), 'Snapshot is not a directory')
        self.records, self.sources = {}, {}
        self.read_count = self.read_bytes = 0
        self.read_digest = hashlib.sha256()
        index_bytes = abd_inputs.bound(self.root, 'manifest/index.json',
                                       verify.INDEX_PIN[1], verify.INDEX_PIN[0])
        index = decode(index_bytes)
        shards = set()
        for shard in index['shards']:
            name = shard['path']
            need(name.startswith('manifest/') and name not in shards, 'Invalid/duplicate manifest shard')
            shards.add(name)
            raw = abd_inputs.bound(self.root, name, shard['sha256'], shard['bytes'])
            lines = raw.splitlines()
            need(len(lines) == shard['entries'], 'Shard entry count mismatch')
            for line in lines:
                row = decode(line)
                name, size, sha = row['path'], row['bytes'], row['sha256']
                rel = PurePosixPath(name)
                need(isinstance(name, str) and not rel.is_absolute() and '..' not in rel.parts
                     and str(rel) == name and '\\' not in name and name not in self.records,
                     'Invalid/duplicate manifest path')
                need(type(size) is int and size >= 0 and isinstance(sha, str) and len(sha) == 64
                     and all(c in '0123456789abcdef' for c in sha), 'Invalid manifest pin')
                self.records[name] = (size, sha)
                source = row['source']
                if source is not None:
                    need(isinstance(source, str) and source.startswith('/'), 'Invalid source alias')
                    old = self.sources.get(source)
                    need(old is None or self.records[old] == (size, sha), 'Conflicting source alias')
                    self.sources[source] = name
        need(len(self.records) == index['total_files'] == verify.EXPECTED_FILES
             and sum(p[0] for p in self.records.values()) == index['total_bytes'] == verify.EXPECTED_BYTES,
             'Archive manifest census differs')

    def pin(self, relative):
        size, sha = self.records[relative]
        return {'path': relative, 'bytes': size, 'sha256': sha}

    def read(self, relative, expected=None):
        size, sha = self.records[relative]
        if expected is not None:
            need(expected['sha256'] == sha and expected.get('bytes', size) == size,
                 'Reference disagrees with archive pin: ' + relative)
        raw = abd_inputs.bound(self.root, relative, sha, size)
        self.read_count += 1
        self.read_bytes += len(raw)
        self.read_digest.update((json.dumps(self.pin(relative), sort_keys=True) + '\n').encode())
        return raw

    def json(self, relative, expected=None):
        return decode(self.read(relative, expected))

    def reference(self, ref):
        need(isinstance(ref.get('path'), str) and ref['path'] in self.sources,
             'Historical source missing from archive source map')
        relative = self.sources[ref['path']]
        return relative, self.json(relative, ref)


def summary_ref(row):
    ref = row['result']
    return ref if isinstance(ref, dict) else {'path': ref, 'sha256': row['sha256']}


def executor_row(row):
    need(row['status'] == 'UNSAT' and row['classification'] == 'UNSAT_EXECUTOR'
         and row['runner_returncode'] == 0 and row['resource_red'] is False,
         'Executor summary is not clean UNSAT')


def family_results(snapshot, family, cases):
    """Select required original terminals, retaining exact continuation ownership."""
    if family == 'D_UUU':
        return {cid: {'ref': c['historical_control'], 'source': 'original'} for cid, c in cases.items()}, []
    if family == 'D_UUT':
        path = 'evidence/D/UUT/full_native_000/RESULT.json'
        term = snapshot.json(path)
        need(term['status'] == 'ALL_EXECUTOR_UNSAT_PENDING_REVIEW' and term['error'] is None
             and not term['never_launched_case_ids'] and not term['unrecorded_case_ids']
             and term['unreconciled_attempt'] is None and not term['received_signals']
             and not term['signals_sent'], 'UUT terminal is incomplete')
        rows = indexed(term['recorded_results'], family)
        exact_cover(cases, rows)
        out = {}
        for cid, row in rows.items():
            pilot = row.get('source') == 'accepted matched pilot'
            need(row['status'] == 'UNSAT' and (pilot or row['runner_returncode'] == 0), 'UUT row not UNSAT')
            need(pilot == (cid == PILOT_CASE) and (not pilot or cases[cid]['pilot_input_matches_accepted']),
                 'UUT pilot owner mismatch')
            out[cid] = {'ref': summary_ref(row), 'source': 'pilot' if pilot else 'original',
                        'summary_cpu': row['cpu_seconds']}
        return out, [snapshot.pin(path)]
    path = (f'evidence/{family}/native_000/RESULT.json' if family in ('A', 'B') else
            f'evidence/D/mixed/uncapped_continuation_000/full_native_{family[2:]}_000/RESULT.json')
    term = snapshot.json(path)
    need(term['status'] == 'ALL_NATIVE_UNSAT_PENDING_FINAL_REVIEW' and term['error'] is None
         and term['unreconciled_attempt'] is None, 'Family terminal is incomplete')
    for key in ('unlaunched_case_ids', 'unresolved_case_ids', 'attempted_without_accepted_terminal',
                'received_signals', 'signals_sent'):
        need(not term[key], 'Unresolved family terminal field: ' + key)
    manifest = abd_inputs.MANIFESTS[family]
    manifest_path, _ = snapshot.reference(term['manifest'])
    need(manifest_path == manifest[0] and term['manifest']['sha256'] == manifest[2], 'Terminal manifest mismatch')
    current = indexed(term['recorded_results'], family)
    need(len(term['attempted_case_ids']) == len(current)
         and set(term['attempted_case_ids']) == set(current), 'Attempt/result census mismatch')
    out, parents = {}, [snapshot.pin(path)]
    for cid, row in current.items():
        executor_row(row)
        out[cid] = {'ref': summary_ref(row), 'source': 'original' if family in ('A', 'B') else 'continuation',
                    'summary_cpu': row['cpu_seconds']}
    if family in ('A', 'B'):
        exact_cover(cases, current)
        return out, parents
    adoption_path, adoption = snapshot.reference(term['predecessor_adoption'])
    need(adoption['decision'] == 'GO_CONTINUE' and adoption['failure'] is None, 'Invalid predecessor adoption')
    _, am = snapshot.reference(adoption['manifest'])
    need(adoption['manifest']['sha256'] == manifest[2], 'Predecessor manifest mismatch')
    inherited = indexed(adoption['accepted_unsat'], 'predecessor adoption')
    for ids in (adoption['accepted_unsat_case_ids'], term['accepted_predecessor_unsat_case_ids']):
        need(len(ids) == len(inherited) and set(ids) == set(inherited), 'Adoption owner census mismatch')
    exact_cover(cases, current, inherited)
    old_path, old = snapshot.reference(adoption['old_terminal'])
    old_rows = indexed(old['recorded_results'], 'predecessor terminal')
    need(set(inherited) <= set(old_rows), 'Adopted owner has no original terminal row')
    for cid, accepted in inherited.items():
        row, case = old_rows[cid], cases[cid]
        executor_row(row)
        need(accepted['status'] == 'UNSAT' and accepted['reaped'] is True and accepted['raw_returncode'] == 20,
             'Adoption is not terminal UNSAT')
        need(all(accepted[k] == case[k] for k in ('cnf_sha256', 'cnf_bytes', 'variables', 'clauses')),
             'Adoption formula mismatch')
        ref = summary_ref(row)
        need(all(ref[k] == accepted['native_result'][k] for k in ('bytes', 'sha256')),
             'Adoption/result reference mismatch')
        need(abs(row['cpu_seconds'] - accepted['cpu_seconds']) < 1e-6, 'Adoption CPU mismatch')
        out[cid] = {'ref': ref, 'source': 'predecessor', 'summary_cpu': row['cpu_seconds']}
    parents.extend([snapshot.pin(adoption_path), snapshot.pin(old_path)])
    return out, parents


def unsat_log(raw):
    need([line.strip() for line in raw.decode('utf-8').splitlines() if line.startswith('s ')]
         == ['s UNSATISFIABLE'], 'Solver log is not exactly one UNSAT status')


def native_result(snapshot, family, formula, selected):
    path, result = snapshot.reference(selected['ref'])
    cid = formula['case_id']
    folder = str(PurePosixPath(path).parent)
    need(result['status'] == 'UNSAT', 'Native result is not UNSAT')
    if family == 'D_UUU':
        need(path == f'evidence/D/UUU/results/{cid}/RESULT.json', 'UUU result owner mismatch')
        need(result['case_id'] == cid and result['solver_exit_code'] == 20 and result['phase'] == 'complete'
             and result['kissat']['s_line'] == 'UNSATISFIABLE', 'UUU native status/exit mismatch')
        mat = result['materialize']
        need(mat['dense_sha256'] == formula['sha256'] and mat['dense_bytes'] == formula['bytes']
             and mat['dense_header'] == [formula['variables'], formula['clauses']], 'UUU input identity mismatch')
        need(result['kissat_sha256'] == KISSAT_SHA and result['kissat_version'] == '4.0.4', 'UUU solver mismatch')
        start = snapshot.json(folder + '/START.json')
        need(start['case_id'] == cid and start['dense_sha256'] == formula['sha256']
             and start['kissat_sha256'] == KISSAT_SHA and start['command'] == result['command'],
             'UUU start/result mismatch')
        log_path = folder + '/kissat.log'
        raw = snapshot.read(log_path)
        need(len(raw) == result['bytes']['solver_log'], 'UUU log size mismatch')
        unsat_log(raw)
        logs = [snapshot.pin(log_path)]
        cpu = result['timing']['cpu_user_seconds'] + result['timing']['cpu_sys_seconds']
    else:
        need(result['schema'] == 'SHARED_NEIGHBORHOOD_NATIVE_PROBE_RESULT_1', 'Unknown native record schema')
        native = result['native']
        need(native['returncode'] == 20 and native['raw_wait_status'] == 5120 and native['signal'] is None
             and result['reaped'] is True and result['terminal']['status_line'] == 'UNSATISFIABLE'
             and not result['received_signals'] and not result['signals_sent'], 'Native status/exit mismatch')
        claim = snapshot.json(folder + '/CLAIM.json')
        need(result['claim'] == claim and result['job_id'] == claim['job_id'] == claim['arguments']['job_id'],
             'Native claim mismatch')
        if selected['source'] == 'pilot':
            expected_job = PILOT_JOB
            need(family == 'D_UUT' and cid == PILOT_CASE and path == 'evidence/D/UUT/native_000/RESULT.json',
                 'Unexpected pilot owner')
        else:
            prefix = {'A': 'SELECTED_A', 'B': 'SELECTED_B', 'D_UUT': 'UUT_FULL_000'}.get(family)
            if prefix is None:
                prefix = family[2:] + ('_UNCAPPED' if selected['source'] == 'continuation' else '_MIXED')
            expected_job = prefix + '/' + cid
        need(result['job_id'] == expected_job, 'Native case owner mismatch')
        args = claim['arguments']
        expected = {k: formula[k] for k in ('bytes', 'sha256', 'variables', 'clauses')}
        need(all(result['input']['census'][k] == v for k, v in expected.items()), 'Native input hash/dimensions mismatch')
        need(result['input_posthash'] == {k: formula[k] for k in ('bytes', 'sha256')}, 'Native input posthash mismatch')
        need(all(args[k] == formula[v] for k, v in
                 [('cnf_sha256', 'sha256'), ('cnf_bytes', 'bytes'), ('variables', 'variables'), ('clauses', 'clauses')]),
             'Claim input hash/dimensions mismatch')
        need(args['cnf'] == result['input']['path'] and result['input_transport'] ==
             'inherited read-only fd; /dev/fd path; original fd held until posthash', 'Input custody mismatch')
        need(result['solver']['sha256'] == args['solver_sha256'] == KISSAT_SHA and
             result['solver_posthash'] == {'bytes': result['solver']['bytes'], 'sha256': KISSAT_SHA}, 'Solver identity mismatch')
        logs = []
        for name in ('stdout.log', 'stderr.log'):
            log_path = folder + '/' + name
            raw = snapshot.read(log_path, result['logs'][name])
            if name == 'stdout.log':
                unsat_log(raw)
            else:
                need(raw == b'', 'Nonempty native stderr')
            logs.append(snapshot.pin(log_path))
        need(result['unsat_certificate_checked'] is False and result['kernel_credit'] is False, 'Unexpected certificate scope')
        cpu = native['cpu_seconds']
        need(abs(cpu - selected['summary_cpu']) < 1e-6 and
             abs(cpu - native['user_cpu_seconds'] - native['system_cpu_seconds']) < 1e-6, 'Native CPU accounting mismatch')
    need(type(cpu) in (int, float) and math.isfinite(cpu) and cpu >= 0, 'Invalid native CPU time')
    return {'family': family, **formula, 'source': selected['source'], 'result': snapshot.pin(path),
            'logs': logs, 'solver_sha256': KISSAT_SHA, 'status': 'UNSAT', 'exit_code': 20,
            'native_CPU_seconds': cpu}


def run(root):
    start, wall = time.process_time(), time.monotonic()
    snapshot = Snapshot(root)
    families, overall = [], hashlib.sha256()
    for name in abd_inputs.MANIFESTS:
        f = abd_inputs.Family(snapshot.root, name)
        cases = indexed(f.cases, name)
        selected, parents = family_results(snapshot, name, cases)
        family_digest, input_digest = hashlib.sha256(), hashlib.sha256()
        sources, cpu = collections.Counter(), 0.0
        for case in f.cases:
            _, formula = f.formula(case)
            row = native_result(snapshot, name, formula, selected[case['case_id']])
            packed = (json.dumps(row, sort_keys=True, separators=(',', ':')) + '\n').encode()
            family_digest.update(packed); overall.update(packed)
            input_digest.update((json.dumps(formula, sort_keys=True, separators=(',', ':')) + '\n').encode())
            sources[row['source']] += 1
            cpu += row['native_CPU_seconds']
        families.append({'family': name, 'formulas': len(cases), 'native_UNSAT': len(cases),
                         'manifest': snapshot.pin(f.relative), 'terminal_parents': parents,
                         'native_sources': dict(sources), 'native_CPU_seconds': cpu,
                         'ordered_formula_records_sha256': input_digest.hexdigest(),
                         'ordered_native_joins_sha256': family_digest.hexdigest()})
        del f, cases, selected
    need(sum(f['formulas'] for f in families) == 56374, 'Final formula census mismatch')
    scripts = []
    for path in (Path(__file__), Path(abd_inputs.__file__), Path(verify.__file__)):
        raw = path.read_bytes()
        scripts.append({'path': 'reproduce/' + path.name, 'bytes': len(raw), 'sha256': digest(raw)})
    return {'schema': 'RAMSEY61_PORTABLE_ABD_NATIVE_JOIN_1', 'status': 'PASS_ALL_56374_NATIVE_UNSAT_JOINS',
            'created_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(), 'families': families,
            'formulas': 56374, 'native_UNSAT': 56374, 'solver_sha256': KISSAT_SHA,
            'ordered_native_joins_sha256': overall.hexdigest(),
            'archive_manifest_index': {'bytes': verify.INDEX_PIN[0], 'sha256': verify.INDEX_PIN[1]},
            'archive_manifest_files': len(snapshot.records), 'consumed_record_reads': snapshot.read_count,
            'consumed_record_bytes': snapshot.read_bytes, 'ordered_record_reads_sha256': snapshot.read_digest.hexdigest(),
            'source_files': scripts, 'CPU_seconds': time.process_time() - start,
            'elapsed_seconds': time.monotonic() - wall,
            'peak_RSS_bytes': resource.getrusage(resource.RUSAGE_SELF).ru_maxrss * (1 if sys.platform == 'darwin' else 1024),
            'solver_calls': 0, 'certificate_replays': 0, 'Lean_calls': 0, 'complete_case_CNFs_written': 0,
            'original_source_reads': 0,
            'scope': 'Every required A/B/D formula reconstructed, then joined by complete SHA256, byte size, '
                     'variable/clause counts and owner to its original terminal native UNSAT record and authenticated '
                     'solver log. Mixed-D predecessor adoption and the UUT pilot are checked explicitly. '
                     'Historical paths resolve only through the pinned archive source map. This checks recorded '
                     'native evidence, not solver correctness, refutation certificates or mathematical coverage. '
                     'Unrelated archive payloads are not rehashed; run reproduce/verify.py full for archive census.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--snapshot', required=True, type=Path)
    parser.add_argument('--receipt', type=Path)
    args = parser.parse_args()
    result = run(args.snapshot)
    raw = (json.dumps(result, indent=2, sort_keys=True) + '\n').encode()
    if args.receipt:
        abd_inputs.exclusive_output(args.snapshot.resolve(strict=True), args.receipt, (raw,))
    print(raw.decode(), end='')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, OSError, KeyError, IndexError, TypeError) as error:
        print('FAIL: ' + str(error), file=sys.stderr)
        sys.exit(1)
