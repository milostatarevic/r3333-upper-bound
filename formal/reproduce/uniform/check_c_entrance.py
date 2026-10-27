#!/usr/bin/env python3
"""Bind all346 Lean-emitted C entrance units to their exact native inputs.

The checker verifies the complete ordered C-specific identifier boundary,
ordered signed physical units, and full DIMACS hashes. It runs no Lean or
solver; run_binding.py separately authenticates the emitter's build library.
"""
import argparse
from collections import Counter
import gzip
import hashlib
import json
from pathlib import Path

BASE_CLAUSES = 156770
BASE_SHA256 = 'f974e4a1e44ae758ba748fc91838cd820cfb807ed4c09e7ffa5dc661d267565e'
# Ordered representative counts for each foreign-type/support-shape boundary.
HEADERS = {
    'UU': {'455': (4,), '545': (4,), '554': (4,), '555': (2,)},
    'UT': {'455': (16,), '545': (16,), '554': (4,6,6,4), '555': (4,)},
    'TT': {'455': (76,), '545': (16,30,30,16), '554': (16,30,30,16), '555': (16,)},
}


def require(ok, message):
    if not ok:
        raise ValueError(message)


def pin(path):
    path = Path(path)
    require(path.is_file() and not path.is_symlink(), 'Expected regular file: '+str(path))
    data = path.read_bytes()
    return {'sha256': hashlib.sha256(data).hexdigest(), 'bytes': len(data)}


def expected_ids():
    return [f'{owner}/{shape}/pair_{p:03d}/rep_{j:03d}'
            for owner, shapes in HEADERS.items() for shape, counts in shapes.items()
            for p, count in enumerate(counts) for j in range(count)]


def check(base_path, unit_path, catalog_path):
    base_path, unit_path, catalog_path = map(Path, (base_path, unit_path, catalog_path))
    before = {name: pin(path) for name, path in
              (('base', base_path), ('lean_units', unit_path), ('catalog', catalog_path))}
    base = base_path.read_bytes()
    require(before['base']['sha256'] == BASE_SHA256 and base.count(b'\n') == BASE_CLAUSES,
            'Shared good-coloring base mismatch')
    expected = expected_ids()
    emitted, emitted_ids = {}, []
    for line in unit_path.read_text().splitlines():
        values = line.split()
        require(len(values) >= 3, 'Malformed Lean C row')
        cid, length, *values = values
        require(cid not in emitted, 'Duplicate Lean C case')
        units = list(map(int, values))
        require(len(units) == int(length), 'Lean unit count mismatch')
        require(all(0 < abs(v) <= 7320 for v in units), 'Non-edge Lean unit')
        require(len(set(units)) == len(units) and not set(units).intersection(-v for v in units),
                'Duplicate or contradictory Lean physical facts')
        emitted[cid] = units
        emitted_ids.append(cid)
    require(emitted_ids == expected, 'Incomplete or reordered Lean C entrance boundary')
    seen, counts, owners, shapes = [], Counter(), Counter(), Counter()
    case_hashes = hashlib.sha256()
    with gzip.open(catalog_path, 'rt') as stream:
        for text in stream:
            row = json.loads(text)
            if row['family'] != 'C':
                continue
            cid = row['case_id']
            require(cid in emitted and cid not in seen, 'Unknown or duplicate catalog C case')
            seen.append(cid)
            require(type(row['units']) is list and all(type(v) is int for v in row['units']),
                    'Malformed catalog C unit list')
            require(row['units'] == emitted[cid], 'Ordered physical unit mismatch: '+cid)
            units = emitted[cid]
            header = f'p cnf 7320 {BASE_CLAUSES+len(units)}\n'.encode()
            suffix = ''.join(f'{v} 0\n' for v in units).encode()
            digest = hashlib.sha256(header+base+suffix).hexdigest()
            require(row['formula'] == {'sha256': digest, 'bytes': len(header)+len(base)+len(suffix),
                                      'variables': 7320, 'clauses': BASE_CLAUSES+len(units)},
                    'Full DIMACS identity mismatch: '+cid)
            owner, shape, _, _ = cid.split('/')
            counts[len(units)] += 1; owners[owner] += 1; shapes[shape] += 1
            case_hashes.update((cid+'\t'+digest+'\n').encode('ascii'))
    require(seen == expected, 'Incomplete or reordered catalog C entrance boundary')
    require(dict(counts) == {430:96, 434:228, 444:22}, 'Physical-unit census mismatch')
    for name, path in (('base', base_path), ('lean_units', unit_path), ('catalog', catalog_path)):
        require(pin(path) == before[name], 'Binding input changed during check: '+name)
    return {'schema': 'UNIFORM_K61_LEAN_C_ENTRANCE_BINDING_1', 'status': 'PASS',
            'cases': 346, 'family_counts': {'C':346}, 'foreign_counts':dict(owners),
            'shape_counts':dict(shapes), 'base_clauses':BASE_CLAUSES, 'variables':7320,
            'base_sha256':before['base']['sha256'], 'lean_units_sha256':before['lean_units']['sha256'],
            'catalog_sha256':before['catalog']['sha256'], 'inputs':before,
            'catalog_order_case_hashes_sha256':case_hashes.hexdigest(),
            'unit_occurrence_counts':dict(sorted(counts.items())), 'checker':pin(__file__),
            'solver_calls':0,
            'scope':'Exact ordered C entrance units and complete DIMACS identities; no native UNSAT claim.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base',type=Path,required=True)
    parser.add_argument('--units',type=Path,required=True)
    parser.add_argument('--catalog',type=Path,required=True)
    parser.add_argument('--output',type=Path)
    args = parser.parse_args()
    report = check(args.base,args.units,args.catalog)
    data = json.dumps(report,indent=2)+'\n'
    if args.output:
        with args.output.open('x') as stream:
            stream.write(data)
    print(data,end='')


if __name__ == '__main__':
    main()
