#!/usr/bin/env python3
"""Independently re-emit the D base clause specification and compare frozen bytes.

No campaign source is imported, no solver or certificate checker is run, and
no finite support/matrix cover or per-leaf suffix is checked. Authenticate the
complete evidence snapshot separately. The receipt must be a new file outside it.
"""
import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
import io
from itertools import combinations
import json
from pathlib import Path
import sys
import time

MANIFESTS = {
    'UUT': ('evidence/D/UUT/full_inputs_000/MANIFEST.json',
            '6ac1fa05c9f5013afade79be9842c36fbc9efa2b0af9aaa2f719b8e2ec20bd12'),
    'UTU': ('evidence/D/mixed/full_inputs_UTU_000/MANIFEST.json',
            'b58f50c345e3007f22abea3a0dd1eff029ee50e2a2e5154a6077553aab2988ac'),
    'UTT': ('evidence/D/mixed/full_inputs_UTT_000/MANIFEST.json',
            'fff1c142c445f3f329a5ea466592ace3271623993bafd1f1f737791406f7d8c7'),
    'TTU': ('evidence/D/mixed/full_inputs_TTU_000/MANIFEST.json',
            'a656853526685c105102fb6962dc71c6777887ffbf5c63d6b2c07e41a4791736'),
    'TTT': ('evidence/D/mixed/full_inputs_TTT_000/MANIFEST.json',
            'd3ea189543e97ca6fc95981ebaa8d317fe464e0f12e8872fdb446a72170b64ec'),
}
TEMPLATES = ('mathematics/retained/LITERAL_U_T_MATRICES.json',
             'd278b344d4fbcaf892c41cd3c843b302844d54766d9489427e3a89fcd24f4d13')
DIFF = (0, 0, 1, 1, 2, 2, 2, 1, 0, 2, 0, 1, 0, 1, 2, 0)
TRADE = {21, 22, 28, 31, 37, 38, 44, 47, 88, 91, 104, 107, 140, 143, 188, 191}
BASE_CLAUSES = {'four': 87311, 'five': 343368}
SPARSE_VARIABLES = {'four': 6000054, 'five': 358915769}
DENSE_VARIABLES = {'four': 4900, 'five': 131570}


def need(condition, message):
    if not condition:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def pair(a, b):
    return b * b + a if a < b else a * a + a + b


def edge(a, b, q):
    a, b = sorted((a, b))
    return pair(pair(a, b), q) + 1


def aux(tag, i, j):
    return pair(tag, pair(i, j)) + 1


def template(kind, a, b):
    q = DIFF[a ^ b]
    return (0, 2, 1)[q] if kind == 'T' and 16 * min(a, b) + max(a, b) in TRADE else q


def counter_specs():
    for a in range(5):
        for q in range(4):
            yield 2704 + 8 * a + q, 15 if q == 0 else 13, [edge(a, v, q) for v in range(5, 51)]
            yield 2708 + 8 * a + q, 35 if q == 0 else 39, [
                edge(a, v, r) for r in range(4) if r != q for v in range(5, 51)]
    yield 2745, 10, [edge(v, 50, 3) for v in range(5, 50)]
    yield 2749, 36, [edge(v, 50, q) for q in range(3) for v in range(5, 50)]


def sequential(tag, bound, inputs):
    n = len(inputs)
    for i, x in enumerate(inputs):
        yield (-x, aux(tag, i, 0))
    for i in range(n - 1):
        for j in range(bound + 1):
            yield (-aux(tag, i, j), aux(tag, i + 1, j))
    for i in range(n - 1):
        for j in range(bound):
            yield (-inputs[i + 1], -aux(tag, i, j), aux(tag, i + 1, j + 1))
    yield (-aux(tag, n - 1, bound),)


def clauses(kind, component):
    k = 4 if component == 'four' else 5
    n = k + 46
    for a, b in combinations(range(n), 2):
        yield 'edge_at_least_one', tuple(edge(a, b, q) for q in range(4))
    for a, b in combinations(range(n), 2):
        for q, r in combinations(range(4), 2):
            yield 'edge_at_most_one', (-edge(a, b, q), -edge(a, b, r))
    for a, b, c in combinations(range(n), 3):
        for q in range(4):
            yield 'triangle', (-edge(a, b, q), -edge(a, c, q), -edge(b, c, q))
    for typ, size, start, palette in zip(kind, (15, 15, 16), (k, k + 15, k + 30),
                                       ((0, 2, 3), (0, 1, 3), (0, 1, 2))):
        for a, b in combinations(range(size), 2):
            yield 'template', (edge(start + a, start + b, palette[template(typ, a, b)]),)
    for a, b in combinations(range(k), 2):
        yield 'free_zero_forbidden', (-edge(a, b, 0),)
    if k == 5:
        for a in range(5):
            yield 'free_mark_color_three', (edge(a, 50, 3),)
        for a, b in combinations(range(5), 2):
            q = 1 if b == a + 1 or (a, b) == (0, 4) else 2
            yield 'free_cycle', (edge(a, b, q),)
        for tag, bound, inputs in counter_specs():
            for clause in sequential(tag, bound, inputs):
                yield 'sequential_counter', clause


def emit(kind, component, mapping=None):
    stream, counts, used = io.BytesIO(), Counter(), set()
    for role, clause in clauses(kind, component):
        counts[role] += 1
        used.update(abs(x) for x in clause)
        if mapping is not None:
            clause = tuple(mapping[abs(x)] * (1 if x > 0 else -1) for x in clause)
        stream.write((' '.join(map(str, clause)) + ' 0\n').encode('ascii'))
    need(sum(counts.values()) == BASE_CLAUSES[component], 'Generated clause count mismatch')
    need(max(used) == SPARSE_VARIABLES[component], 'Generated sparse variable maximum mismatch')
    if mapping is not None:
        need(used == set(mapping), 'Dense map includes missing/unused atoms')
    return stream.getvalue(), dict(counts)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--snapshot', required=True, type=Path)
    parser.add_argument('--receipt', required=True, type=Path)
    args = parser.parse_args()
    root = args.snapshot.resolve(strict=True)
    need(root.is_dir(), 'Snapshot is not a directory')
    receipt = args.receipt.parent.resolve(strict=True) / args.receipt.name
    need(receipt != root and root not in receipt.parents, 'Receipt must be outside snapshot')
    need(not receipt.exists() and not receipt.is_symlink(), 'Receipt already exists')
    started = time.process_time()
    pins, comparisons = [], []

    def read(relative, digest, size=None):
        rel = Path(relative)
        need(not rel.is_absolute() and '..' not in rel.parts, 'Invalid evidence path')
        path = root / rel
        need(all(not p.is_symlink() for p in (path, *path.parents) if p != root), 'Symlink in source path')
        before = path.stat()
        need(path.is_file() and before.st_size <= 64 << 20, 'Invalid evidence file')
        data = path.read_bytes()
        after = path.stat()
        need((before.st_ino, before.st_size, before.st_mtime_ns) ==
             (after.st_ino, after.st_size, after.st_mtime_ns), 'Source changed during read')
        need(sha(data) == digest and (size is None or len(data) == size), 'Pin mismatch: ' + str(rel))
        pins.append({'path': str(rel), 'sha256': digest, 'bytes': len(data)})
        return data

    def compare(kind, component, label, relative, pin, expected, counts):
        actual = read(relative, pin['sha256'], pin['bytes'])
        need(actual == expected, 'Clause specification mismatch: ' + label)
        comparisons.append({'owner': kind, 'component': component, 'label': label,
                            'path': str(relative), 'bytes': len(actual), 'sha256': sha(actual),
                            'base_clauses': sum(counts.values()), 'clause_families': counts})

    literal_templates = json.loads(read(*TEMPLATES))
    need({r['kind'] for r in literal_templates} == {'U', 'T'}, 'Template owner set')
    for record in literal_templates:
        expected = [[-1 if a == b else template(record['kind'], a, b) for b in range(16)]
                    for a in range(16)]
        need(record['matrix'] == expected, 'Literal template convention mismatch')

    manifest_path, manifest_sha = MANIFESTS['UUT']
    manifest = json.loads(read(manifest_path, manifest_sha))
    directory = Path(manifest_path).parent
    for kind in ('UUU', 'UUT'):
        for component in ('four', 'five'):
            parent = manifest['parents'][component]
            pin = parent['original' if kind == 'UUU' else 'uut_sparse_base']
            relative = (Path('support/workspace') / pin['path'].split('/r77-findings/', 1)[1]
                        if kind == 'UUU' else directory / pin['relative_path'])
            body, counts = emit(kind, component)
            header = f'p cnf {SPARSE_VARIABLES[component]} {BASE_CLAUSES[component]}\n'.encode()
            compare(kind, component, kind + '/' + component + '/sparse', relative, pin, header + body, counts)

    for kind in ('UTU', 'UTT', 'TTU', 'TTT'):
        manifest_path, manifest_sha = MANIFESTS[kind]
        manifest = json.loads(read(manifest_path, manifest_sha))
        directory, cache = Path(manifest_path).parent, {}
        expected_stages = {'P15_MATRIX_ONLY', 'D9_FIRST4', 'D10'}
        if kind.startswith('UT'):
            expected_stages.add('D9_SECOND4')
        need(set(manifest['prefixes']) == expected_stages, 'Prefix stage set mismatch')
        for stage, pin in sorted(manifest['prefixes'].items()):
            component = 'four' if stage == 'P15_MATRIX_ONLY' else 'five'
            map_pin = pin['dense_map']
            inverse = json.loads(read(directory / Path(map_pin['path']).name,
                                     map_pin['sha256'], map_pin['bytes']))['dense_to_sparse']
            need(inverse[0] == 0 and len(inverse) == DENSE_VARIABLES[component] + 1 and
                 all(type(x) is int and x > 0 for x in inverse[1:]) and
                 len(set(inverse)) == len(inverse), 'Dense map is not a bijection')
            if component not in cache:
                mapping = {sparse: dense for dense, sparse in enumerate(inverse) if dense}
                cache[component] = emit(kind, component, mapping), inverse
            (body, counts), previous = cache[component]
            need(previous == inverse, 'Stages disagree on dense map')
            units = {'P15_MATRIX_ONLY': 91, 'D9_FIRST4': 95, 'D9_SECOND4': 95, 'D10': 105}[stage]
            nc = BASE_CLAUSES[component] + units
            need(pin['base_clauses'] == BASE_CLAUSES[component] and pin['clauses'] == nc and
                 pin['variables'] == DENSE_VARIABLES[component], 'Prefix dimensions mismatch')
            header = f'p cnf {DENSE_VARIABLES[component]} {nc}\n'.encode()
            compare(kind, component, kind + '/' + stage + '/dense_prefix',
                    directory / Path(pin['path']).name, pin, header + body, counts)

    need(len(comparisons) == 18, 'Incomplete comparison set')
    result = {'schema': 'RAMSEY61_D_BASE_SPEC_CHECK_1', 'status': 'PASS_EXACT_D_BASE_SPECIFICATION',
              'checked_at_utc': datetime.now(timezone.utc).isoformat(),
              'checker_sha256': sha(Path(__file__).read_bytes()), 'CPU_seconds': time.process_time() - started,
              'owners': ['UUU', 'UUT', 'UTU', 'UTT', 'TTU', 'TTT'],
              'distinct_owner_component_bases': 12, 'stored_base_or_prefix_comparisons': 18,
              'five_base_counter_blocks': 42, 'five_base_counter_clauses': 250788,
              'source_pins': pins, 'comparisons': comparisons,
              'new_solver_calls': 0, 'certificate_checked': False, 'lean_built': False,
              'mathematical_coverage_proved': False, 'leaf_suffixes_checked': False,
              'scope': 'Independent re-emission of every ordered base clause for all six D owners; '
                       'exact sparse bytes for UUU/UUT and exact mapped dense prefix bytes for mixed D. '
                       'No finite support/matrix orbit coverage, per-leaf suffix, native answer, or full formal bridge checked.'}
    with receipt.open('x') as stream:
        json.dump(result, stream, indent=2, sort_keys=True)
        stream.write('\n')
    print(json.dumps({k: v for k, v in result.items() if k not in ('source_pins', 'comparisons')}, indent=2))


if __name__ == '__main__':
    try:
        main()
    except (OSError, ValueError, KeyError, IndexError, TypeError) as error:
        print('FAIL: ' + str(error), file=sys.stderr)
        sys.exit(1)
