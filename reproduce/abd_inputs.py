#!/usr/bin/env python3
"""Reconstruct the frozen original A/B/D inputs, without importing campaign code.

This checks byte identity, not mathematical coverage or UNSAT. No solver is run.
An authenticated, extracted evidence-v1 snapshot is the only input dependency.
"""
import argparse
import hashlib
import io
import json
import os
from pathlib import Path
import re
import shutil
import stat
import sys
import time

LIMIT = 64 << 20
FLOOR = 100 << 30
MANIFESTS = {
    'A': ('evidence/A/full_inputs_000/MANIFEST.json', 360, '04b63427c743d41369cd305fd82e37450bc26c4d5262b47ddd20b4544d8ced13'),
    'B': ('evidence/B/full_inputs_000/MANIFEST.json', 5096, '717eddaab19150f9e6443c06180fdcaf655ebdd89a9ce43056d2aa8ae054fa66'),
    'D_UUU': ('evidence/D/UUT/full_inputs_000/MANIFEST.json', 679, '6ac1fa05c9f5013afade79be9842c36fbc9efa2b0af9aaa2f719b8e2ec20bd12'),
    'D_UUT': ('evidence/D/UUT/full_inputs_000/MANIFEST.json', 679, '6ac1fa05c9f5013afade79be9842c36fbc9efa2b0af9aaa2f719b8e2ec20bd12'),
    'D_UTU': ('evidence/D/mixed/full_inputs_UTU_000/MANIFEST.json', 6576, 'b58f50c345e3007f22abea3a0dd1eff029ee50e2a2e5154a6077553aab2988ac'),
    'D_UTT': ('evidence/D/mixed/full_inputs_UTT_000/MANIFEST.json', 6576, 'fff1c142c445f3f329a5ea466592ace3271623993bafd1f1f737791406f7d8c7'),
    'D_TTU': ('evidence/D/mixed/full_inputs_TTU_000/MANIFEST.json', 18204, 'a656853526685c105102fb6962dc71c6777887ffbf5c63d6b2c07e41a4791736'),
    'D_TTT': ('evidence/D/mixed/full_inputs_TTT_000/MANIFEST.json', 18204, 'd3ea189543e97ca6fc95981ebaa8d317fe464e0f12e8872fdb446a72170b64ec'),
}


def need(ok, message):
    if not ok:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def inside(root, relative):
    p = Path(relative)
    need(not p.is_absolute() and '..' not in p.parts, 'Unsafe evidence path')
    target = root / p
    for part in (target, *target.parents):
        if part == root:
            break
        need(not part.is_symlink(), 'Symlink in evidence path')
    return target


def bound(root, relative, digest, size=None):
    p = inside(root, relative)
    before = p.stat()
    need(stat.S_ISREG(before.st_mode) and before.st_size <= LIMIT, 'Invalid source size/type')
    with p.open('rb') as f:
        data = f.read(LIMIT + 1)
    after = p.stat()
    need((before.st_ino, before.st_size, before.st_mtime_ns) ==
         (after.st_ino, after.st_size, after.st_mtime_ns), 'Source changed during read')
    need(sha(data) == digest and (size is None or len(data) == size), 'Source hash/size mismatch: ' + str(relative))
    return data


def units_bytes(units, variables):
    need(isinstance(units, list) and all(type(x) is int and 0 < abs(x) <= variables for x in units), 'Invalid unit literal')
    need(len({abs(x) for x in units}) == len(units), 'Repeated or conflicting unit')
    return ''.join(f'{x} 0\n' for x in units).encode('ascii')


def header(nv, nc):
    return f'p cnf {nv} {nc}\n'.encode('ascii')


def exclusive_output(root, path, blocks):
    path = Path(path).absolute()
    parent = path.parent.resolve(strict=True)
    dest = parent / path.name
    need(dest != root and root not in dest.parents, 'Output must be outside the immutable snapshot')
    need(shutil.disk_usage(parent).free >= FLOOR + sum(map(len, blocks)), '100 GiB disk floor')
    fd = os.open(dest, os.O_WRONLY | os.O_CREAT | os.O_EXCL | getattr(os, 'O_NOFOLLOW', 0), 0o600)
    # Preserve partial output on an error: never delete or replace evidence.
    with os.fdopen(fd, 'wb') as f:
        for b in blocks:
            f.write(b)
        f.flush()
        os.fsync(f.fileno())
    h = hashlib.sha256()
    size = 0
    with dest.open('rb') as f:
        for b in iter(lambda: f.read(1 << 20), b''):
            size += len(b)
            h.update(b)
    expected = hashlib.sha256()
    for b in blocks:
        expected.update(b)
    need(size == sum(map(len, blocks)) and h.digest() == expected.digest(), 'Persisted output mismatch')
    return {'bytes': size, 'sha256': h.hexdigest(), 'path': str(dest)}


class Family:
    def __init__(self, root, family):
        self.root, self.family = root, family
        self.relative, self.count, self.manifest_sha = MANIFESTS[family]
        self.directory = str(Path(self.relative).parent)
        self.manifest = json.loads(bound(root, self.relative, self.manifest_sha))
        self.cases = self.manifest['cases']
        need(len(self.cases) == self.count and len({c['case_id'] for c in self.cases}) == self.count, 'Case census mismatch')
        self.cache = {}
        self.bases = {}

    def ordinary_prefix(self, case):
        key = case['prefix_key']
        if key not in self.cache:
            pin = self.manifest['prefixes'][key]
            name = Path(pin['path']).name
            rel = self.directory + ('/prefixes/' if self.family in ('A', 'B') else '/') + name
            data = bound(self.root, rel, pin['sha256'], pin['bytes'])
            first = data.split(b'\n', 1)[0]
            m = re.fullmatch(rb'p cnf (\d+) (\d+) *', first)
            need(m and tuple(map(int, m.groups())) == (pin['variables'], pin['clauses']), 'Prefix header mismatch')
            need(data.endswith(b'\n') and data.count(b'\n') == pin['base_clauses'] + 1, 'Prefix clause count mismatch')
            self.cache[key] = data, hashlib.sha256(data)
        pin = self.manifest['prefixes'][key]
        need(case['variables'] == pin['variables'] and case['clauses'] == pin['clauses'] and
             len(case['dense_units']) + pin['base_clauses'] == case['clauses'], 'Case/prefix dimensions mismatch')
        suffix = units_bytes(case['dense_units'], case['variables'])
        need(sha(suffix) == case['suffix_sha256'], 'Suffix digest mismatch')
        return self.cache[key], suffix, case['cnf_sha256'], case['cnf_bytes']

    def original_base(self, component):
        if component in self.bases:
            return self.bases[component]
        parent = self.manifest['parents'][component]
        mp = parent['dense_map']
        mapping_record = json.loads(bound(self.root, self.directory + '/' + mp['relative_path'], mp['sha256'], mp['bytes']))
        inverse = mapping_record['dense_to_sparse']
        need(inverse[0] == 0 and len(inverse) == parent['variables_dense'] + 1 and
             len(set(inverse)) == len(inverse), 'Dense map not bijective')
        mapping = {x: i for i, x in enumerate(inverse) if i}
        if self.family == 'D_UUT':
            pin = parent['uut_sparse_base']
            rel = self.directory + '/' + pin['relative_path']
            body_sha = parent['uut_dense_body_sha256']
        else:
            pin = parent['original']
            original_tail = pin['path'].split('/r77-findings/', 1)
            need(len(original_tail) == 2, 'Original base relocation missing')
            rel = 'support/workspace/' + original_tail[1]
            body_sha = parent['original_dense_body_sha256']
        sparse = bound(self.root, rel, pin['sha256'], pin['bytes'])
        stream = io.BytesIO(sparse)
        need(stream.readline() == header(parent['variables_sparse'], parent['clauses']), 'Sparse header mismatch')
        dense = io.BytesIO()
        count = 0
        for line in stream:
            tokens = list(map(int, line.split()))
            need(tokens and tokens[-1] == 0 and all(abs(x) in mapping for x in tokens[:-1]), 'Sparse atom outside map')
            literals = [mapping[abs(x)] if x > 0 else -mapping[abs(x)] for x in tokens[:-1]]
            dense.write((' '.join(map(str, literals)) + ' 0\n').encode('ascii'))
            count += 1
        body = dense.getvalue()
        need(count == parent['clauses'] and sha(body) == body_sha, 'Dense base mismatch')
        self.bases[component] = parent, mapping, body
        return self.bases[component]

    def historical_prefix(self, case):
        parent, mapping, body = self.original_base(case['parent_component'])
        need(case['variables'] == parent['variables_dense'] and case['clauses'] == parent['clauses'] + len(case['units']), 'Historical dimensions')
        sparse_suffix = units_bytes(case['units'], parent['variables_sparse'])
        need(sha(sparse_suffix) == case['units_sha256'], 'Historical units mismatch')
        dense_units = [mapping[abs(x)] if x > 0 else -mapping[abs(x)] for x in case['units']]
        suffix = units_bytes(dense_units, case['variables'])
        key = case['parent_component'], case['clauses']
        if key not in self.cache:
            data = header(case['variables'], case['clauses']) + body
            self.cache[key] = data, hashlib.sha256(data)
        if self.family == 'D_UUU':
            # Bind the reconstructed old control to its actual native result.
            control = case['historical_control']
            rel = 'evidence/D/UUU/results/' + case['case_id'] + '/RESULT.json'
            result = json.loads(bound(self.root, rel, control['sha256'], control['bytes']))
            expected = case['old_virtual_dense_sha256']
            need(result['case_id'] == case['case_id'] and result['status'] == 'UNSAT' and
                 result['solver_exit_code'] == 20 and result['materialize']['dense_sha256'] == expected,
                 'UUU historical native control mismatch')
            size = result['materialize']['dense_bytes']
        else:
            expected, size = case['cnf_sha256'], case['cnf_bytes']
        return self.cache[key], suffix, expected, size

    def formula(self, case):
        (prefix, state), suffix, expected, size = (self.historical_prefix(case)
            if self.family in ('D_UUU', 'D_UUT') else self.ordinary_prefix(case))
        h = state.copy()
        h.update(suffix)
        need(h.hexdigest() == expected and len(prefix) + len(suffix) == size, 'Complete formula hash/size mismatch: ' + case['case_id'])
        return (prefix, suffix), {'case_id': case['case_id'], 'sha256': expected, 'bytes': size,
            'variables': case['variables'], 'clauses': case['clauses']}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('command', choices=('list', 'verify-all', 'materialize'))
    p.add_argument('--snapshot', required=True, type=Path)
    p.add_argument('--family', choices=tuple(MANIFESTS))
    p.add_argument('--case')
    p.add_argument('--output', type=Path)
    p.add_argument('--receipt', type=Path)
    a = p.parse_args()
    root = a.snapshot.resolve(strict=True)
    need(root.is_dir(), 'Snapshot is not a directory')
    start = time.process_time()
    if a.command != 'verify-all':
        need(a.family is not None, '--family is required')
    if a.command == 'materialize':
        need(a.case is not None and a.output is not None, '--case and --output are required')
    families = [a.family] if a.family else list(MANIFESTS)
    results = []
    for name in families:
        f = Family(root, name)
        if a.command == 'list':
            print(json.dumps({'family': name, 'count': f.count, 'cases': [c['case_id'] for c in f.cases]}, indent=2))
            return
        cases = f.cases if a.command == 'verify-all' else [c for c in f.cases if c['case_id'] == a.case]
        need(cases and (a.command == 'verify-all' or len(cases) == 1), 'Unknown/duplicate requested case')
        digest = hashlib.sha256()
        logical_bytes = 0
        for case in cases:
            blocks, row = f.formula(case)
            digest.update((json.dumps(row, sort_keys=True, separators=(',', ':')) + '\n').encode())
            logical_bytes += row['bytes']
            if a.command == 'materialize':
                row['output'] = exclusive_output(root, a.output, blocks)
                results.append({'family': name, **row})
        if a.command == 'verify-all':
            results.append({'family': name, 'formulas': len(cases), 'logical_formula_bytes': logical_bytes,
                'ordered_formula_records_sha256': digest.hexdigest(), 'manifest_sha256': f.manifest_sha})
        del f
    receipt = {'schema': 'RAMSEY61_PORTABLE_ABD_INPUTS_1', 'status': 'PASS_EXACT_INPUT_BYTES',
        'command': a.command, 'families': results, 'CPU_seconds': time.process_time() - start,
        'new_solver_calls': 0, 'certificate_checked': False, 'mathematical_coverage_proved': False,
        'scope': 'Input reconstruction/hash verification only; authenticate complete evidence separately.'}
    data = (json.dumps(receipt, indent=2, sort_keys=True) + '\n').encode()
    if a.receipt:
        exclusive_output(root, a.receipt, (data,))
    print(data.decode(), end='')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, OSError, KeyError, IndexError) as e:
        print('FAIL: ' + str(e), file=sys.stderr)
        sys.exit(1)
