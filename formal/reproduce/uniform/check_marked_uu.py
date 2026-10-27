#!/usr/bin/env python3
"""Bind all 1,358 direct Lean U/U suffixes to exact UNIFORM-K61 input bytes."""
import argparse
from collections import Counter
import gzip
import hashlib
import json
from pathlib import Path
import time

BASE_SHA = 'f974e4a1e44ae758ba748fc91838cd820cfb807ed4c09e7ffa5dc661d267565e'
COUNTS = {'D_UUU': 679, 'D_UUT': 679}


def need(ok, message):
    if not ok:
        raise ValueError(message)


def pin(path):
    data = Path(path).read_bytes()
    return {'path': str(path), 'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}


def case_indices(path, manifest):
    record = pin(path)
    expected = manifest['sources']['D_UU']
    need(expected['path'] == 'reproduce/data/marked_uu.json'
         and all(record[k] == expected[k] for k in ('bytes','sha256')), 'Case-table pin mismatch')
    data = json.loads(path.read_text())
    need(data['schema'] == 'UNIFORM_K61_MARKED_UU_DATA_1', 'Case-table schema')
    rows = data['cases']
    need(len(rows) == 679 and sorted(row['index'] for row in rows) == list(range(679))
         and len({row['case_id'] for row in rows}) == 679, 'Case-table bijection')
    return {row['case_id']: row['index'] for row in rows}, record


def check(inputs, emission, case_table):
    started = time.process_time()
    manifest_path, base_path = inputs/'MANIFEST.json', inputs/'base.clauses'
    catalog_path = inputs/'cases.jsonl.gz'
    watched = [pin(path) for path in (manifest_path,base_path,catalog_path,case_table)]
    manifest = json.loads(manifest_path.read_text())
    indices, table_pin = case_indices(case_table, manifest)
    base = base_path.read_bytes()
    need(pin(base_path)['sha256'] == BASE_SHA == manifest['base']['sha256'], 'Base mismatch')
    need(base.count(b'\n') == 156770, 'Base clause count mismatch')
    need(pin(catalog_path)['sha256'] == manifest['catalog']['sha256'], 'Catalog pin mismatch')
    expected, counts = {}, Counter()
    with gzip.open(catalog_path, 'rt') as stream:
        for line in stream:
            row = json.loads(line)
            family = row['family']
            if family not in COUNTS:
                continue
            need(row['case_id'] in indices, 'Unknown marked case identity')
            key = family, indices[row['case_id']]
            need(key not in expected, 'Duplicate marked catalog owner: ' + str(key))
            expected[key] = row
            counts[family] += 1
    need(dict(counts) == COUNTS, 'Incomplete marked catalog census')
    need(set(expected) == {(family, i) for family in COUNTS for i in range(679)},
         'Incomplete marked Leaf bijection')
    need({p.name for p in emission.iterdir()} == {'UUU.tsv', 'UUT.tsv'}, 'Unexpected emission files')
    states, seen, artifacts = {}, set(), []
    digest = hashlib.sha256()
    for owner in ('UUU', 'UUT'):
        path = emission/(owner+'.tsv')
        need(path.is_file() and path.stat().st_size <= 64 << 20, 'Invalid emission file')
        artifacts.append(pin(path))
        lines = path.read_text(encoding='ascii').splitlines()
        need(len(lines) == 680 and lines[0] == f'MARKED_UU\t{owner}\t679', 'Incomplete Lean emission')
        for text in lines[1:]:
            fields = text.split('\t')
            need(len(fields) == 4 and fields[0] == 'LEAF', 'Malformed Lean leaf')
            index, length = int(fields[1]), int(fields[2])
            key = 'D_'+owner, index
            need(key in expected and key not in seen, 'Unknown or duplicate Lean leaf: ' + str(key))
            seen.add(key)
            units = list(map(int, fields[3].split(',')))
            need(len(units) == length and all(0 < abs(v) <= 7320 for v in units), 'Invalid physical units')
            row = expected[key]
            need(units == row['units'], 'Ordered unit mismatch: ' + str(key))
            suffix = ''.join(f'{v} 0\n' for v in units).encode('ascii')
            if length not in states:
                prefix = f'p cnf 7320 {156770+length}\n'.encode('ascii') + base
                states[length] = hashlib.sha256(prefix), len(prefix)
            state, size = states[length]
            h = state.copy(); h.update(suffix)
            observed = {'sha256': h.hexdigest(), 'bytes': size+len(suffix),
                        'variables': 7320, 'clauses': 156770+length}
            need(observed == row['formula'], 'Full formula mismatch: ' + str(key))
            digest.update((key[0]+'\t'+row['case_id']+'\t'+h.hexdigest()+'\n').encode('ascii'))
    need(seen == set(expected), 'Incomplete Lean-to-input binding')
    for record in watched+artifacts:
        need(pin(record['path']) == record, 'Binding input changed: '+record['path'])
    return {'schema': 'UNIFORM_K61_MARKED_UU_BINDING_1', 'status': 'PASS',
            'cases': len(seen), 'family_counts': dict(counts),
            'ordered_case_hashes_sha256': digest.hexdigest(),
            'inputs_manifest': pin(manifest_path), 'catalog': pin(catalog_path), 'base': pin(base_path),
            'emission_shards': artifacts, 'emitter': pin(Path(__file__).with_name('EmitMarkedUU.lean')),
            'checker': pin(Path(__file__)), 'case_table':table_pin, 'CPU_seconds': time.process_time()-started,
            'solver_calls': 0,
            'scope': 'Exact ordered Lean case units, complete Leaf/case-ID bijection, and full DIMACS hashes. Shared Lean base binding is checked separately.'}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--inputs', type=Path, required=True)
    p.add_argument('--emission', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--case-table', type=Path, required=True)
    a = p.parse_args()
    need(not a.output.exists(), 'Refusing to replace a binding result')
    result = check(a.inputs, a.emission, a.case_table)
    a.output.parent.mkdir(parents=True, exist_ok=True)
    with a.output.open('x') as stream:
        json.dump(result, stream, indent=2); stream.write('\n')
    print(json.dumps({k:v for k,v in result.items() if k != 'emission_shards'}, indent=2))


if __name__ == '__main__':
    main()
