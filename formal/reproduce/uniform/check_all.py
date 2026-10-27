#!/usr/bin/env python3
"""Join all 56,723 Lean-emitted uniform inputs without running a solver.

This checks bytes and exhaustive ownership. Use run_binding.py to additionally
bind emitter execution to a successful current-source portable Lean build.
"""
import argparse
from collections import Counter
import gzip
import hashlib
import json
from pathlib import Path
import subprocess
import sys

COUNTS = {'A':360, 'B':5096, 'D_UUU':679, 'D_UUT':679, 'D_UTU':6576,
          'D_UTT':6576, 'D_TTU':18204, 'D_TTT':18204, 'C':346, 'BALANCE':3}


def need(ok, message):
    if not ok:
        raise ValueError(message)


def pin(path):
    h, size = hashlib.sha256(), 0
    with Path(path).open('rb') as stream:
        for data in iter(lambda: stream.read(1 << 20), b''):
            h.update(data); size += len(data)
    return {'path':str(path), 'sha256':h.hexdigest(), 'bytes':size}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--inputs', type=Path, required=True)
    p.add_argument('--c-base', type=Path, required=True)
    p.add_argument('--c-units', type=Path, required=True)
    p.add_argument('--common', type=Path, required=True)
    p.add_argument('--marked-uu', type=Path, required=True)
    p.add_argument('--balance', type=Path, required=True)
    p.add_argument('--case-table', type=Path, required=True)
    p.add_argument('--output-dir', type=Path, required=True)
    a = p.parse_args()
    need(not a.output_dir.exists(), 'Output directory must be fresh')
    a.output_dir.mkdir(parents=True)
    manifest_pin = pin(a.inputs/'MANIFEST.json')
    base_pin = pin(a.inputs/'base.clauses')
    manifest = json.loads((a.inputs/'MANIFEST.json').read_text())
    need(manifest['schema'] == 'UNIFORM_K61_INPUTS_2' and manifest['cases'] == 56723
         and manifest['family_counts'] == COUNTS and manifest['complete_family_counts'] == COUNTS,
         'Complete current input manifest required')
    catalog = a.inputs/'cases.jsonl.gz'
    catalog_pin = pin(catalog)
    need(catalog_pin['sha256'] == manifest['catalog']['sha256'], 'Catalog pin mismatch')
    need(a.c_base.read_bytes() == (a.inputs/'base.clauses').read_bytes(), 'Lean and production shared bases differ')
    owners, counts = set(), Counter()
    digest = hashlib.sha256()
    with gzip.open(catalog, 'rt') as stream:
        for line in stream:
            row = json.loads(line)
            key = row['family'], row['case_id']
            need(key not in owners, 'Duplicate input owner')
            owners.add(key); counts[key[0]] += 1
            digest.update(('\t'.join(key)+'\t'+row['formula']['sha256']+'\n').encode('ascii'))
    need(dict(counts) == COUNTS and len(owners) == 56723, 'Whole census differs')
    here = Path(__file__).resolve().parent
    commands = [
        ('common', [str(here/'check_common.py'), '--inputs', str(a.inputs), '--emission', str(a.common)]),
        ('marked_uu', [str(here/'check_marked_uu.py'), '--inputs', str(a.inputs), '--emission', str(a.marked_uu), '--case-table', str(a.case_table)]),
        ('c', [str(here/'check_c_entrance.py'), '--base', str(a.c_base), '--units', str(a.c_units), '--catalog', str(catalog)]),
        ('balance', [str(here/'check_balance.py'), '--inputs', str(a.inputs), '--emission', str(a.balance)]),
    ]
    reports, receipts = {}, []
    for name, arguments in commands:
        output = a.output_dir/(name+'.json')
        command = [sys.executable, '-I', '-B'] + arguments + ['--output', str(output)]
        with (a.output_dir/(name+'.log')).open('xb') as log:
            completed = subprocess.run(command, stdout=log, stderr=subprocess.STDOUT, check=False)
        need(completed.returncode == 0, 'Binding check failed: '+name+'; see retained log')
        report = json.loads(output.read_text())
        expected_status = 'PASS_ALL_55016_UNIFORM_COMMON_INPUTS' if name == 'common' else 'PASS'
        need(report['status'] == expected_status, 'Invalid binding status')
        reported_catalog = report['catalog']['sha256'] if name != 'c' else report['catalog_sha256']
        need(reported_catalog == catalog_pin['sha256'], 'Binding checks used different catalogs')
        reports[name] = report; receipts.append(pin(output))
    need(reports['common']['cases'] == 55016 and reports['marked_uu']['cases'] == 1358
         and reports['c']['cases'] == 346 and reports['balance']['cases'] == 3, 'Binding case union differs')
    need({**reports['common']['family_counts'], **reports['marked_uu']['family_counts'],
          **reports['c']['family_counts'], **reports['balance']['family_counts']} == COUNTS,
         'Family covers are incomplete or overlap')
    need(pin(catalog) == catalog_pin, 'Catalog changed during checks')
    need(pin(a.inputs/'MANIFEST.json') == manifest_pin, 'Input manifest changed during checks')
    need(pin(a.inputs/'base.clauses') == base_pin, 'Input base changed during checks')
    result = {'schema':'UNIFORM_K61_ALL_INPUT_BINDING_1', 'status':'PASS_ALL_56723_INPUTS',
              'cases':56723, 'family_counts':dict(counts), 'catalog':catalog_pin,
              'inputs_manifest':manifest_pin, 'lean_base':pin(a.c_base),
              'catalog_order_case_hashes_sha256':digest.hexdigest(), 'component_receipts':receipts,
              'checker':pin(Path(__file__)), 'solver_calls':0,
              'scope':'Exact ordered unit lists and full DIMACS identities for the complete disjoint case cover. Operational execution binding, not a kernel proof of serialization or UNSAT.'}
    with (a.output_dir/'BINDING_RESULT.json').open('x') as stream:
        json.dump(result, stream, indent=2); stream.write('\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
