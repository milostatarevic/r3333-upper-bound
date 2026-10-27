#!/usr/bin/env python3
"""Bind three Lean-emitted complete balanced formulas to the current inputs.

This checks exact bytes and the exhaustive owner boundary. The fresh-build
binding driver separately authenticates the Lean emitter and its runtime.
"""
import argparse
import gzip
import hashlib
import json
from pathlib import Path

OWNERS = ('UU', 'UT', 'TT')


def need(ok, message):
    if not ok:
        raise ValueError(message)


def pin(path):
    path = Path(path)
    need(path.is_file() and not path.is_symlink(), 'Expected regular file: '+str(path))
    h, size = hashlib.sha256(), 0
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(1 << 20), b''):
            h.update(block); size += len(block)
    return {'sha256': h.hexdigest(), 'bytes': size}


def check(inputs, emission):
    inputs, emission = Path(inputs), Path(emission)
    need(emission.is_dir() and not emission.is_symlink(), 'Expected emission directory')
    need({p.name for p in emission.iterdir()} == {owner+'.cnf' for owner in OWNERS},
         'Balanced emission file census')
    catalog = inputs/'cases.jsonl.gz'
    catalog_pin = pin(catalog)
    with gzip.open(catalog, 'rt') as stream:
        rows = [row for line in stream if (row := json.loads(line))['family'] == 'BALANCE']
    need([row['case_id'] for row in rows] == list(OWNERS), 'Balanced catalog owner boundary')
    files = []
    for row in rows:
        owner = row['case_id']
        need(row['file'] == f'balanced/{owner}.cnf', 'Balanced catalog path')
        emitted = emission/(owner+'.cnf')
        native = inputs/row['file']
        emitted_pin = pin(emitted)
        native_pin = pin(native)
        need(emitted_pin == native_pin, 'Lean/native byte mismatch: '+owner)
        need(row['formula'] == {**emitted_pin, 'variables':13656, 'clauses':524462},
             'Balanced formula identity mismatch: '+owner)
        count = 0
        with emitted.open('rb') as source:
            need(source.readline() == b'p cnf 13656 524462\n', 'Balanced Lean header')
            for text in source:
                clause = list(map(int, text.split()))
                need(len(clause) >= 2 and clause[-1] == 0
                     and all(0 < abs(lit) <= 13656 for lit in clause[:-1]), 'Balanced literal range')
                count += 1
        need(count == 524462, 'Balanced clause census')
        need(pin(emitted) == emitted_pin and pin(native) == native_pin, 'Input changed during binding')
        files.append({'case_id':owner, 'emitted':emitted_pin, 'native':native_pin,
                      'variables':13656, 'clauses':count})
    need(pin(catalog) == catalog_pin, 'Catalog changed during binding')
    return {'schema':'UNIFORM_K61_LEAN_BALANCE_BINDING_1', 'status':'PASS', 'cases':3,
            'family_counts':{'BALANCE':3}, 'catalog':catalog_pin, 'files':files,
            'checker':pin(__file__), 'solver_calls':0,
            'scope':'Exact complete DIMACS identities for all three balanced owners; no native UNSAT claim.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--inputs', type=Path, required=True)
    parser.add_argument('--emission', type=Path, required=True)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    report = check(args.inputs, args.emission)
    text = json.dumps(report, indent=2)+'\n'
    if args.output:
        with args.output.open('x') as stream:
            stream.write(text)
    print(text, end='')


if __name__ == '__main__':
    main()
