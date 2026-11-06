#!/usr/bin/env python3
"""Bind and archive the simplified K60 formal boundary, without SAT calls.

The four bind commands execute unchanged Lean emitters against one checked
build. Prepare retains source, build receipts and complete emissions; verify
checks those retained bytes without executing Lean or archived programs. Build
receipts are execution provenance, not a replay of the Lean kernel.
"""
import argparse
from collections import Counter
import datetime as dt
import hashlib
import importlib.util
import json
import os
from pathlib import Path, PurePosixPath
import posixpath
import re
import shutil
import subprocess
import sys
import time
import unittest

import formal_evidence as historical

SCHEMA = 'K60_PUBLICATION_FORMAL_1'
BINDING_SCHEMA = 'K60_PUBLICATION_INPUT_BINDING_1'
TOTAL = 296081
MODULE_COUNT = 1314
TARGET = 'UniformK60.Verification'
ORIGINAL_NATIVE_SHA = '089599c2c4ed17524bb73727584391f16f85272facaf283d3923e4938f770d95'
ORIGINAL_FORMAL_SHA = '652a69a00fae00c0e49969556e646b1ba2fa223057d2791ef2206ac3e49051a2'
COMPOSITE_SCHEMA = 'K60_PUBLICATION_COMPOSITE_BUILD_1'
BASE_SHA = historical.BASE_SHA
CATALOGUES = historical.CATALOGUES
MIXED = 'balance-simplification-pilot/manifest-pentagon-only.json'
FIVE = 'inputs-balance-fiveguards-all/manifest.json'
MANIFESTS = {MIXED: '1999e8a27e25fdf080509ca028269801e716171f10aac28c1245847974ecc84d',
             FIVE: '5c39d4af5c9a65eafcfafad4db2473edc8a2529983304ab2bad9938302e3c803'}
EMITTERS = {
    'base': ('EmitBase.lean', '233f922e7336b240f62c4d0fc1774f2e7315f15ae7c749259cfdb81f8f3a02c1'),
    'marked': ('EmitMarkedK60.lean', 'b8b75c8030cf6a0ebd38b854c65952e535a3e70b240e600fb0901037e9e330c6'),
    'counter': ('EmitCounters.lean', 'f8a4275e2502dbdc7cebd773c15630b8dbcb96c8de5ea78f99342fc4c7cdf0e9'),
    'balance': ('EmitBalanced.lean', 'de49b9b909a1c15c4cd26df0967bda29fe4a2ebf9e2360fcec6f248f25816365'),
}
PARTS = tuple(EMITTERS)
REQUIRED = {'UniformK60.ExactInputs', 'UniformK60.FiniteBoundary', TARGET,
            'UniformK60.BalancedC2Normalize', 'UniformK60.BalancedC1Cover',
            'UniformK60.BalancedEncodingBalance', 'UniformK60.BalancedEncodingSoundness',
            'UniformK60.BalancedEncodingData', 'UniformK60.BalancedEncodingAllFive',
            'UniformK60.CEntranceComplete', 'UniformK60.SequentialCounter',
            'UniformK61.CommonUnitCache'}
TRUST = ('Conditional Lean reduction with exact-input binding provenance for 296081 formulas. '
         'Archived receipts are provenance, not a replay of Lean. Native UNSAT evidence '
         'is verified separately; this capsule makes no SAT-campaign completion claim.')
require = historical.require
read_json = historical.read_json
digest = historical.sha


def utc():
    return dt.datetime.now(dt.timezone.utc).isoformat()


def member(value):
    return historical.safe_member(value)


def origin(value):
    return historical.absolute_origin(value)


def regular(path):
    path = Path(path)
    require(path.is_file() and not path.is_symlink() and path == path.resolve(),
            'Expected canonical regular file: ' + str(path))
    return path


def pin(path):
    return historical.pin(regular(path))


def checked(path, record):
    actual = pin(path)
    require(actual['sha256'] == record['sha256'] and
            ('bytes' not in record or actual['bytes'] == record['bytes']),
            'Changed file: ' + str(path))
    return Path(path)


def write_once(path, value):
    with Path(path).open('x') as stream:
        json.dump(value, stream, indent=2, sort_keys=True); stream.write('\n')


def relative(base, value):
    require(isinstance(value, str) and not PurePosixPath(value).is_absolute()
            and '\\' not in value, 'Invalid relative input reference')
    return str(member(posixpath.normpath(str(PurePosixPath(base).parent / value))))


class Inputs:
    """Read only exact input members authenticated by the original native release."""
    def __init__(self, root):
        self.root = Path(root).resolve(strict=True)
        top = regular(self.root / 'NATIVE_RELEASE.json')
        if pin(top)['sha256'] == ORIGINAL_NATIVE_SHA:
            self.authority = top
        else:
            require(read_json(top).get('schema') == 'K60_SELECTED_NATIVE_EVIDENCE_1',
                    'Unknown native capsule input authority')
            self.authority = regular(self.root / 'provenance/NATIVE_RELEASE-original.json')
        require(pin(self.authority)['sha256'] == ORIGINAL_NATIVE_SHA,
                'Wrong original native manifest')
        self.manifest = read_json(self.authority)
        self.used = {}

    def path(self, rel, expected=None):
        rel = str(member(rel)); require(rel in self.manifest['files'], 'Input absent from original manifest')
        record = self.manifest['files'][rel]
        if expected is not None:
            require(record['sha256'] == expected, 'Wrong expected input identity: ' + rel)
        path = checked(self.root / rel, record)
        self.used[rel] = record
        return path

    def pilot(self, rel, expected=None):
        return self.path('workspace/k60-pilot/' + str(member(rel)), expected)

    def json(self, rel, expected=None):
        return read_json(self.pilot(rel, expected))

    def unchanged(self):
        checked(self.authority, {'sha256': ORIGINAL_NATIVE_SHA})
        for rel, record in self.used.items(): checked(self.root / rel, record)


def proof_sources(formal):
    manifest_path = regular(formal / 'SOURCE_MANIFEST.json')
    manifest = read_json(manifest_path)
    require(manifest['roots'] == [TARGET] and len(manifest['modules']) == MODULE_COUNT
            and REQUIRED <= set(manifest['modules']), 'Wrong selected source closure')
    require(manifest['toolchain'] == 'leanprover/lean4:v4.32.1'
            and manifest['mathlib_rev'] == '520045ab14e26149ee970e2e617ca04b09bde5d6',
            'Wrong compiler/dependency policy')
    require(not any('BalancedEncodingBrace' in n or 'BalancedHostBrace' in n or
                    'BalancedProjected' in n for n in manifest['modules']),
            'Historical marked-balance sources remain in selected closure')
    files = {'SOURCE_MANIFEST.json': pin(manifest_path)}
    for group in ('files', 'data'):
        entries = manifest[group]
        entries = entries.items() if isinstance(entries, dict) else ((r['path'], r) for r in entries)
        for rel, record in entries:
            rel = str(member(rel)); checked(formal / rel, record); files[rel] = pin(formal / rel)
    texts = {}
    for name, record in manifest['modules'].items():
        rel = 'src/' + name.replace('.', '/') + '.lean'
        require(record['path'] == rel, 'Noncanonical proof source path')
        path = checked(formal / rel, record); files[rel] = pin(path)
        text = path.read_text(); texts[name] = text; code = historical.lean_code(text)
        require(historical.imports_of(text) == record['imports'], 'Source imports differ')
        require(not re.search(r'\b(sorry|admit|axiom|native_decide|sorryAx)\b', code), 'Unproved proof source')
        if name == 'R4333Lean.CheckedLRAT':
            require(pin(path)['sha256'] == '0dc50a516ce88c897aa9c1b71baedb1f693b010cdd644886f83dd09fd677edc5',
                    'Reviewed LRAT helper changed')
        else:
            require(not re.search(r'\b(unsafe|partial|implemented_by|extern|ofReduceBool|ofReduceNat|trustCompiler)\b|#eval\b|\brun_elab\b|debug\.skipKernelTC', code),
                    'Unreviewed proof execution escape: ' + name)
        for embedded in historical.embedded_paths(text):
            full = (path.parent / embedded).resolve()
            require(full.is_relative_to(formal) and str(full.relative_to(formal)) in files,
                    'Embedded data lacks source-manifest custody')
    visited = set()
    def visit(name):
        if name in visited: return
        require(name in texts, 'Missing project import: ' + name); visited.add(name)
        for dep in manifest['modules'][name]['imports']:
            if dep.split('.')[0] in {x.split('.')[0] for x in texts}: visit(dep)
    visit(TARGET); require(visited == set(texts), 'Omitted or unrelated selected source')
    historical.audit_signatures(texts)
    code = re.sub(r'\s+', '', historical.lean_code(texts['UniformK60.ExactInputs']))
    require('abbrevAllFiveCase:=Fin3' in code
            and 'defallFiveOwner:AllFiveCase→BalancedHost.Owner:=![(false,false),(false,true),(true,true)]' in code
            and 'abbrevCase:=ABDFormula.Case⊕EFormula.Case⊕CEntranceFormula.Case⊕BalancedHost.Owner⊕AllFiveCase' in code
            and '|.inr(.inr(.inr(.inlo)))=>BalancedEncodingData.formulao' in code
            and 'BalancedEncodingBraces' not in code, 'Wrong simplified computational premise')
    for part, (name, wanted) in EMITTERS.items():
        rel = 'reproduce/' + name; checked(formal / rel, {'sha256': wanted}); files[rel] = pin(formal / rel)
    return manifest, texts, files


def accepted_baseline(root):
    archive = historical.Archive(Path(root).resolve(strict=True), ORIGINAL_FORMAL_SHA)
    build, summary = historical.inspect_build(archive, archive.manifest['build_result'])
    require(summary == archive.manifest['summary']['build'], 'Accepted baseline build summary differs')
    return archive, build


def changed_closure(manifest, baseline):
    dirty = {name for name, row in manifest['modules'].items()
             if name not in baseline['sources'] or row['sha256'] != baseline['sources'][name]['sha256']}
    while True:
        larger = dirty | {name for name, row in manifest['modules'].items() if set(row['imports']) & dirty}
        if larger == dirty: break
        dirty = larger
    require(dirty == {'UniformK60.BalancedC2Normalize', 'UniformK60.BalancedEncodingBalance',
                      'UniformK60.ExactInputs', 'UniformK60.FiniteBoundary', TARGET},
            'Unexpected changed/transitive-dependent module set')
    return dirty


def composite_context(formal, result_path, logical_formal, logical_run, live):
    run = result_path.parent; build = read_json(result_path)
    manifest, texts, source_files = proof_sources(formal)
    baseline_root = Path(build['baseline_capsule']) if live else run / 'baseline'
    archive, baseline = accepted_baseline(baseline_root)
    dirty = changed_closure(manifest, baseline); reused = set(texts) - dirty
    require(build['schema'] == COMPOSITE_SCHEMA and build['status'] == 'PASS'
            and build['targets'] == [TARGET] and build['selected_modules'] == MODULE_COUNT
            and build['baseline_manifest_sha256'] == ORIGINAL_FORMAL_SHA
            and build['manifest_sha256'] == source_files['SOURCE_MANIFEST.json']['sha256']
            and build['run'] == logical_run and build['formal'] == logical_formal
            and build['rebuilt_modules'] == sorted(dirty) and build['reused_modules'] == sorted(reused)
            and build['completed'] == sorted(texts) and build['jobs'] == 1
            and build['new_solver_calls'] == 0 and build['baseline_project_artifacts_reused'] is True,
            'Wrong composite build boundary')
    require(build['builder_sha256'] == pin(Path(__file__).resolve())['sha256'], 'Composite builder changed')
    compiler = build['compiler']; compiler_path = baseline['modules'][-1]['command'][3]
    require(compiler['path'] == compiler_path and compiler['sha256'] == baseline['compiler_sha256']
            and compiler['version'] == baseline['compiler'] and compiler['packages'] == baseline['packages'],
            'Composite compiler/dependencies differ from accepted baseline')
    roots = build['LEAN_PATH'].split(os.pathsep)
    require(roots == [logical_run + '/lib', *baseline['lean_path'].split(os.pathsep)[1:]],
            'Composite library contains unreviewed project roots')
    files = {'BUILD_RESULT.json': pin(result_path)}; artifacts = {}; produced = {}
    old = {row['module']: row for row in baseline['modules']}
    def artifact(path, record):
        origin(path)
        require(path not in artifacts or artifacts[path] == record, 'Conflicting composite artifact pins')
        artifacts[path] = record
        if live: checked(Path(path), record)
    artifact(compiler_path, {'sha256': compiler['sha256']})
    pending = set(texts); seen = set()
    while pending:
        ready = sorted(n for n in pending if set(manifest['modules'][n]['imports']) & set(texts) <= seen)
        require(ready, 'Composite import graph stalled')
        for name in ready:
            source = manifest['modules'][name]; folder = run / 'modules' / name
            recpath = regular(folder / 'receipt.json'); row = read_json(recpath)
            logpath = checked(folder / 'lean.log', {'sha256': row['log_sha256']})
            files['modules/' + name + '/receipt.json'] = pin(recpath)
            files['modules/' + name + '/lean.log'] = pin(logpath)
            require(row['module'] == name and row['status'] == 'PASS' and row['source'] == source,
                    'Wrong composite module receipt')
            historical.audit_axioms(logpath.read_text())
            dest = logical_run + '/lib/' + name.replace('.', '/')
            if name in reused:
                prior = old[name]
                require(row['mode'] == 'REUSED_ACCEPTED_BUILD' and row['baseline_record_sha256'] ==
                        digest(json.dumps(prior, sort_keys=True, separators=(',', ':')).encode())
                        and source['sha256'] == baseline['sources'][name]['sha256']
                        and source['imports'] == historical.imports_of(archive.get(baseline['sources'][name]['path']).read_text())
                        and row['log_sha256'] == prior['log_sha256'], 'Reused module differs from accepted proof')
                expected = []
                old_output = prior['artifacts'][0]['path']; old_stem = old_output[:-len('.olean')]
                for record in prior['artifacts']:
                    suffix = record['path'][len(old_stem):]
                    require(suffix in ('.olean', '.olean.private', '.olean.server', '.ir'), 'Unexpected old companion')
                    custody = archive.custody[record['path']]
                    expected.append({'path': dest + suffix, **custody})
                require(row['artifacts'] == expected, 'Reused artifact copy differs')
                for records in prior['imports'].values():
                    for record in records:
                        if not record['path'].startswith(baseline['lean_path'].split(os.pathsep)[0] + '/'):
                            artifact(record['path'], archive.custody[record['path']])
                produced[name] = expected
            else:
                require(row['exit_code'] == 0 and row['cpu_threads'] == 1
                        and row['compiler_sha256'] == compiler['sha256']
                        and row['LEAN_PATH'] == build['LEAN_PATH']
                        and row['command'] == [compiler_path, '-j1', '-o', logical_run + '/modules/' + name + '/output.olean',
                                               logical_formal + '/' + source['path']], 'Wrong rebuilt module execution')
                expected_imports = []
                for dep in source['imports']:
                    if dep in texts: expected_imports.extend(produced[dep])
                    else:
                        suffix = '/' + dep.replace('.', '/') + '.olean'
                        records = [r for r in row['import_artifacts']
                                   if any(r['path'].startswith(root + suffix) or r['path'] == root + suffix[:-len('.olean')] + '.ir'
                                          for root in roots[1:])]
                        require(records and any(r['path'].endswith('.olean') for r in records), 'Missing external rebuild import')
                        for record in records:
                            require(archive.custody.get(record['path']) == {k: record[k] for k in ('sha256', 'bytes')},
                                    'External rebuild import lacks accepted custody')
                        expected_imports.extend(records)
                require(row['import_artifacts'] == expected_imports, 'Rebuild imported stale/unreviewed artifacts')
                output = logical_run + '/modules/' + name + '/output.olean'
                artifact(output, {'sha256': row['artifact_sha256'], 'bytes': row['artifact_bytes']})
                produced[name] = build['rebuilt_artifacts'][name]
                require(produced[name] and produced[name][0] ==
                        {'path': dest + '.olean', 'sha256': row['artifact_sha256'], 'bytes': row['artifact_bytes']},
                        'Wrong rebuilt primary artifact')
                require(len({r['path'] for r in produced[name]}) == len(produced[name]) and
                        all(r['path'] in {dest + x for x in ('.olean', '.olean.private', '.olean.server', '.ir')}
                            for r in produced[name]), 'Wrong rebuilt companion set')
            for record in produced[name]: artifact(record['path'], {k: record[k] for k in ('sha256', 'bytes')})
            seen.add(name); pending.remove(name)
    require(set(build['rebuilt_artifacts']) == dirty, 'Wrong rebuilt artifact census')
    final = (run / 'modules' / TARGET / 'lean.log').read_text()
    require('ExactInputs.AllUnsat' in final and 'NoMonochromaticTriangle' in final, 'Missing final endpoint type')
    for endpoint in ('UniformK60.ramsey60_of_exact_unsat', 'UniformK60.CEntranceComplete.no_entrance_of_all_unsat'):
        hits = re.findall(r"'" + re.escape(endpoint) + r"' depends on axioms:\s*\[([^]]*)\]", final)
        require(len(hits) == 1 and {x.strip() for x in hits[0].split(',')} == historical.AXIOMS,
                'Missing composite endpoint axiom report')
    return {'formal': formal, 'run': run, 'logical_formal': logical_formal, 'logical_run': logical_run,
            'build': build, 'build_result_pin': pin(result_path), 'source_files': source_files,
            'build_files': files, 'artifacts': artifacts, 'lean_path': build['LEAN_PATH'], 'compiler': compiler,
            'baseline_archive': archive}


def build_context(formal, result_path, *, logical_formal=None, logical_run=None, live=True):
    """Check full or composite build provenance and, in live mode, artifact bytes."""
    formal = Path(formal).resolve(strict=True); result_path = regular(Path(result_path).resolve(strict=True))
    run = result_path.parent
    logical_formal = str(formal) if logical_formal is None else str(origin(logical_formal))
    logical_run = str(run) if logical_run is None else str(origin(logical_run))
    require(result_path.name == 'BUILD_RESULT.json', 'Expected final build result')
    if read_json(result_path).get('schema') == COMPOSITE_SCHEMA:
        return composite_context(formal, result_path, logical_formal, logical_run, live)
    manifest, texts, source_files = proof_sources(formal)
    build = read_json(result_path)
    require(build['status'] == 'PASS' and build['targets'] == [TARGET]
            and build['selected_modules'] == MODULE_COUNT and build['jobs'] == 1
            and build['new_solver_calls'] == 0 and build['baseline_project_artifacts_reused'] is False
            and build['completed'] == sorted(manifest['modules']) and not build['pending']
            and not build['failures'] and not build['interrupted'], 'Incomplete or reused project build')
    require(build['manifest_sha256'] == source_files['SOURCE_MANIFEST.json']['sha256']
            and build['run'] == logical_run, 'Build/source identity differs')
    compiler = build['compiler']; origin(compiler['path'])
    require('version 4.32.1,' in compiler['version'], 'Wrong compiler version')
    lake = read_json(formal / 'lake-manifest.json')
    require({p['name']: p['revision'] for p in compiler['packages']} ==
            {p['name']: p['rev'] for p in lake['packages']}, 'Wrong locked dependencies')
    expected_cert = sorted(n for n, text in texts.items()
                           if re.search(r'\b(?:checked_lrat_proof|lrat_proof|lrat)\b', historical.lean_code(text)))
    require(build['certificate_command_modules'] == expected_cert, 'Wrong certificate replay census')
    receipts = {}; artifact_pins = {}; build_files = {'BUILD_RESULT.json': pin(result_path)}
    def artifact(path, record):
        origin(path)
        require(path not in artifact_pins or artifact_pins[path] == record, 'Conflicting artifact pins')
        artifact_pins[path] = record
        if live: checked(Path(path), record)
    artifact(compiler['path'], {'sha256': compiler['sha256']})
    for name, source in manifest['modules'].items():
        rel = 'modules/' + name
        recpath = regular(run / rel / 'receipt.json'); row = read_json(recpath)
        logpath = checked(run / rel / 'lean.log', {'sha256': row['log_sha256']})
        build_files[rel + '/receipt.json'] = pin(recpath); build_files[rel + '/lean.log'] = pin(logpath)
        require(row['module'] == name and row['status'] == 'PASS' and row['exit_code'] == 0
                and row['source'] == source and row['compiler_sha256'] == compiler['sha256']
                and row['cpu_threads'] == 1, 'Invalid module receipt: ' + name)
        output = logical_run + '/' + rel + '/output.olean'
        require(row['command'] == [compiler['path'], '-j1', '-o', output, logical_formal + '/' + source['path']],
                'Unexpected module compile command')
        roots = row['LEAN_PATH'].split(os.pathsep)
        require(roots[0] == logical_run + '/lib' and all(PurePosixPath(p).is_absolute() for p in roots),
                'Fresh build library is not first')
        historical.audit_axioms(logpath.read_text())
        records = row['import_artifacts']; grouped = {}
        for record in records:
            path = record['path']; base = re.sub(r'\.(?:olean(?:\.private|\.server)?|ir)$', '', path)
            grouped.setdefault(base, []).append(record); artifact(path, {k: record[k] for k in ('sha256', 'bytes')})
        expected_imports = set()
        for dep in source['imports']:
            suffix = '/' + dep.replace('.', '/')
            candidates = [logical_run + '/lib' + suffix] if dep in texts else [p + suffix for p in roots[1:]]
            matches = [p for p in candidates if p in grouped]
            require(len(matches) == 1, 'Missing or stale direct import: ' + dep)
            base = matches[0]; expected_imports.add(base)
            require(any(r['path'] == base + '.olean' for r in grouped[base]), 'Missing direct import olean')
            require(len({r['path'] for r in grouped[base]}) == len(grouped[base]), 'Duplicate artifact record')
            if dep in texts:
                dep_row = read_json(run / 'modules' / dep / 'receipt.json')
                primary = next(r for r in grouped[base] if r['path'] == base + '.olean')
                require(primary['sha256'] == dep_row['artifact_sha256'] and
                        primary['bytes'] == dep_row['artifact_bytes'], 'Project import differs from its fresh producer')
        require(set(grouped) == expected_imports, 'Extraneous import artifact')
        artifact(output, {'sha256': row['artifact_sha256'], 'bytes': row['artifact_bytes']})
        if live:
            libpath = Path(logical_run) / 'lib' / Path(*name.split('.')).with_suffix('.olean')
            checked(libpath, {'sha256': row['artifact_sha256'], 'bytes': row['artifact_bytes']})
            for p in [libpath, Path(str(libpath) + '.private'), Path(str(libpath) + '.server'), libpath.with_suffix('.ir')]:
                if p.exists(): artifact(str(p), pin(p))
        receipts[name] = row
    final_log = (run / 'modules' / TARGET / 'lean.log').read_text()
    for endpoint in ('UniformK60.ramsey60_of_exact_unsat', 'UniformK60.CEntranceComplete.no_entrance_of_all_unsat'):
        hits = re.findall(r"'" + re.escape(endpoint) + r"' depends on axioms:\s*\[([^]]*)\]", final_log)
        require(len(hits) == 1 and {x.strip() for x in hits[0].split(',')} == historical.AXIOMS,
                'Missing endpoint axiom audit')
    require('ExactInputs.AllUnsat' in final_log and 'NoMonochromaticTriangle' in final_log, 'Missing endpoint type report')
    return {'formal': formal, 'run': run, 'logical_formal': logical_formal, 'logical_run': logical_run,
            'build': build, 'build_result_pin': pin(result_path), 'source_files': source_files,
            'build_files': build_files, 'artifacts': artifact_pins,
            'lean_path': receipts[TARGET]['LEAN_PATH'], 'compiler': compiler}


def base_body(inputs):
    manifest = inputs.json(CATALOGUES['e'][0], CATALOGUES['e'][2])
    rel = relative(CATALOGUES['e'][0], manifest['base']['path'])
    raw = inputs.pilot(rel, BASE_SHA).read_bytes()
    require(raw.startswith(b'p cnf 7080 149270\n'), 'Wrong K60 base header')
    body = raw.split(b'\n', 1)[1]
    require(body == historical.generated_base(), 'Base differs from independent full K60 construction')
    return body


def prefix_specs(inputs):
    mixed = inputs.json(MIXED, MANIFESTS[MIXED]); five = inputs.json(FIVE, MANIFESTS[FIVE])
    specs = [(p['id'], p, relative(MIXED, p['cnf'])) for p in mixed['prefixes']]
    specs += [('C1_FIVE_' + p['owner'], p, relative(FIVE, p['cnf'])) for p in five['cases']]
    require([x[0] for x in specs] == ['C2_ROOT_' + x for x in ('UU', 'UT', 'TU', 'TT')] +
            ['C1_FIVE_' + x for x in ('UU', 'UT', 'TT')], 'Wrong seven-formula catalogue')
    return specs


def counter_data(inputs):
    mixed = inputs.json(MIXED, MANIFESTS[MIXED]); commands = []; chunks = []; count = 0
    by_id = {p['id']: p for p in mixed['prefixes']}
    # Preserve the accepted counter-emission order; the seven-formula catalogue
    # separately retains its own UU,UT,TU,TT order.
    for name in ('UU', 'TU', 'UT', 'TT'):
        p = by_id['C2_ROOT_' + name]
        raw = inputs.pilot(relative(MIXED, p['cnf']), p['sha256']).read_bytes()
        meta = read_json(inputs.pilot(relative(MIXED, p['metadata']), p['metadata_sha256']))
        lines = raw.splitlines(); top = 7080
        require(lines[0] == f'p cnf {p["variables"]} {p["clauses"]}'.encode() and
                len(lines) == p['clauses'] + 1 and len(meta['cardinalities']) == 240, 'Wrong counter prefix')
        for block in meta['cardinalities']:
            atoms = block['literals']
            require(block['relation'] == 'atmost' and type(block['bound']) is int and block['bound'] >= 0
                    and all(type(a) is int and 0 < a <= 7080 for a in atoms), 'Wrong counter metadata')
            commands.append(' '.join(map(str, [top, block['bound']] + atoms)))
            if block['first_aux'] is None: require(block['last_aux'] is None, 'Wrong empty counter')
            else:
                require(block['first_aux'] == top + 1 and block['last_aux'] >= block['first_aux'], 'Wrong counter allocation')
                top = block['last_aux']
            first, last = block['first_clause'], block['last_clause']
            require(0 < first <= last + 1 <= len(lines), 'Counter range escapes prefix')
            chunks.append(f'c counter {top}\n'.encode())
            chunks.extend(line + b'\n' for line in lines[first:last + 1]); count += last - first + 1
    require(len(commands) == 960, 'Wrong counter block census')
    return ('\n'.join(commands) + '\n').encode(), b''.join(chunks), count


def compare(part, folder, inputs):
    if part == 'base':
        body = base_body(inputs); actual = regular(folder / 'lean-base.body').read_bytes()
        require(actual == body, 'Lean base mismatch')
        return {'clauses': 149270, 'bytes': len(body), 'sha256': digest(body)}
    if part == 'balance':
        rows = []
        for name, spec, rel in prefix_specs(inputs):
            frozen = inputs.pilot(rel, spec['sha256']); emitted = regular(folder / 'prefixes' / (name + '.cnf'))
            require(emitted.read_bytes() == frozen.read_bytes(), 'Whole-prefix mismatch: ' + name)
            header = emitted.open('rb').readline().decode().strip().split()
            require(header[:2] == ['p', 'cnf'], 'Malformed prefix header')
            rows.append({'id': name, **pin(emitted), 'variables': int(header[2]), 'clauses': int(header[3])})
        require({p.name for p in (folder / 'prefixes').iterdir()} == {r['id'] + '.cnf' for r in rows}, 'Unexpected prefix file')
        return {'formulas': 7, 'compatibility_cases': 4, 'all_five_cases': 3, 'rows': rows}
    if part == 'counter':
        data, expected, clauses = counter_data(inputs)
        require(regular(folder / 'inputs.txt').read_bytes() == data and
                regular(folder / 'lean-counters.cnf').read_bytes() == expected, 'Counter emission mismatch')
        return {'blocks': 960, 'prefixes': 4, 'ordered_clauses': clauses, 'sha256': digest(expected)}
    require(part == 'marked', 'Unknown binding part'); body = base_body(inputs); summaries = {}; census = hashlib.sha256(); seeds = {}
    for family, (rel, count, wanted_sha) in CATALOGUES.items():
        manifest = inputs.json(rel, wanted_sha); expected = Counter()
        if family == 'entrances':
            for row in manifest['cases']: expected[(row['family'], row['sha256'])] += 1
        else:
            ledger = inputs.pilot(relative(rel, manifest['hash_index']['path']), manifest['hash_index']['sha256']).read_bytes()
            require(len(ledger) == 34 * count, 'Wrong hash ledger length')
            ordinals = []
            for factor in manifest['factors']:
                owner = ('E_' if family == 'e' else '') + factor['owner']
                ordinals.extend(range(factor['ordinal_start'], factor['ordinal_stop']))
                for i in range(factor['ordinal_start'], factor['ordinal_stop']): expected[(owner, ledger[34*i:34*i+32].hex())] += 1
            require(ordinals == list(range(count)), 'Incomplete factor ledger coverage')
        require(sum(expected.values()) == count, 'Wrong expected marked count')
        observed = Counter(); seen = set(); owners = Counter()
        with regular(folder / 'units' / (family + '.tsv')).open() as stream:
            for line in stream:
                parts = line.rstrip('\n').split('\t'); require(len(parts) == 3, 'Malformed marked emission')
                owner, key, text = parts; require((owner, key) not in seen, 'Duplicate emitted case key'); seen.add((owner, key))
                units = [int(x) for x in text.split(',')]
                require(units and all(0 < abs(x) <= 7080 for x in units) and len(units) == len(set(units))
                        and not set(units) & {-x for x in units}, 'Invalid physical facts')
                require(family == 'entrances' or units == sorted(units), 'Unsorted marked facts')
                h = historical.formula_digest(seeds, body, units); observed[(owner, h)] += 1; owners[owner] += 1
        require(observed == expected, 'Missing, altered or duplicate formula occurrences: ' + family)
        for (owner, h), n in sorted(observed.items()): census.update(f'{family} {owner} {h} {n}\n'.encode())
        summaries[family] = {'cases': count, 'owners': dict(owners)}
    require(sum(x['cases'] for x in summaries.values()) == TOTAL - 7, 'Wrong selected marked boundary')
    return {'families': summaries, 'formula_multiset_sha256': census.hexdigest(), 'formulas': TOTAL - 7}


def emitter_command(part, compiler, formal, folder):
    emitter = str(PurePosixPath(formal) / 'reproduce' / EMITTERS[part][0])
    args = [] if part == 'base' else [str(PurePosixPath(folder) / 'units')] if part == 'marked' else \
        [str(PurePosixPath(folder) / 'inputs.txt'), str(PurePosixPath(folder) / 'lean-counters.cnf')] if part == 'counter' else \
        [str(PurePosixPath(folder) / 'prefixes')]
    return [compiler, '-j1', '--run', emitter, *args]


def verify_live_context(context):
    for rel, record in context['source_files'].items(): checked(context['formal'] / rel, record)
    for rel, record in context['build_files'].items(): checked(context['run'] / rel, record)
    for path, record in context['artifacts'].items(): checked(Path(path), record)


def composite_build(args):
    """Compile exactly the changed dependency closure; preserve honest reuse provenance."""
    formal = args.formal.resolve(strict=True); manifest, texts, sources = proof_sources(formal)
    archive, baseline = accepted_baseline(args.baseline_capsule)
    dirty = changed_closure(manifest, baseline); reused = set(texts) - dirty
    out = args.output.absolute(); require(out == out.resolve(), 'Noncanonical composite output')
    out.mkdir(parents=True, exist_ok=False); lib = out / 'lib'; lib.mkdir()
    compiler_path = baseline['modules'][-1]['command'][3]
    checked(Path(compiler_path), archive.custody[compiler_path])
    compiler = {'path': compiler_path, 'sha256': baseline['compiler_sha256'],
                'version': baseline['compiler'], 'packages': baseline['packages']}
    paths = [Path(x) for x in baseline['lean_path'].split(os.pathsep)[1:]]
    spec = importlib.util.spec_from_file_location('selected_public_build', formal / 'build.py')
    builder = importlib.util.module_from_spec(spec); spec.loader.exec_module(builder)
    old = {row['module']: row for row in baseline['modules']}; watched = {}; produced = {}
    result = {'schema': COMPOSITE_SCHEMA, 'status': 'FAIL', 'started_utc': utc(),
              'run': str(out), 'formal': str(formal), 'targets': [TARGET], 'jobs': 1,
              'selected_modules': MODULE_COUNT, 'new_solver_calls': 0,
              'baseline_project_artifacts_reused': True, 'baseline_capsule': str(archive.root),
              'baseline_manifest_sha256': ORIGINAL_FORMAL_SHA,
              'manifest_sha256': sources['SOURCE_MANIFEST.json']['sha256'],
              'builder_sha256': pin(Path(__file__).resolve())['sha256'], 'compiler': compiler,
              'reused_modules': sorted(reused), 'rebuilt_modules': sorted(dirty),
              'completed': [], 'rebuilt_artifacts': {},
              'LEAN_PATH': os.pathsep.join(map(str, [lib, *paths])),
              'trust': '1309 unchanged checked modules reused; five changed/dependent modules recompiled. Not a fresh full build.'}
    try:
        for name in sorted(reused):
            source = manifest['modules'][name]; prior = old[name]
            require(source['sha256'] == baseline['sources'][name]['sha256'] and
                    source['imports'] == historical.imports_of(archive.get(baseline['sources'][name]['path']).read_text()),
                    'Changed source cannot be reused: ' + name)
            folder = out / 'modules' / name; folder.mkdir(parents=True)
            log = archive.get(prior['log']); shutil.copyfile(log, folder / 'lean.log')
            new_artifacts = []; old_stem = prior['artifacts'][0]['path'][:-len('.olean')]
            new_stem = lib / Path(*name.split('.'))
            for record in prior['artifacts']:
                oldpath = Path(record['path']); custody = archive.custody[record['path']]
                suffix = record['path'][len(old_stem):]
                require(suffix in ('.olean', '.olean.private', '.olean.server', '.ir'), 'Wrong accepted artifact suffix')
                target = Path(str(new_stem) + suffix); copy_checked(oldpath, target, custody)
                new_artifacts.append({'path': str(target), **custody}); watched[str(target)] = custody
            for records in prior['imports'].values():
                for record in records:
                    if not record['path'].startswith(baseline['lean_path'].split(os.pathsep)[0] + '/'):
                        custody = archive.custody[record['path']]
                        if record['path'] not in watched: checked(Path(record['path']), custody)
                        watched[record['path']] = custody
            receipt = {'module': name, 'source': source, 'status': 'PASS', 'mode': 'REUSED_ACCEPTED_BUILD',
                       'baseline_record_sha256': digest(json.dumps(prior, sort_keys=True, separators=(',', ':')).encode()),
                       'artifacts': new_artifacts, 'log_sha256': prior['log_sha256']}
            write_once(folder / 'receipt.json', receipt); produced[name] = new_artifacts
        print(json.dumps({'event': 'authenticated_reuse', 'modules': len(reused)}), flush=True)
        done = set(reused); pending = set(dirty)
        while pending:
            ready = sorted(n for n in pending if set(manifest['modules'][n]['imports']) & set(texts) <= done)
            require(ready, 'Changed dependency graph stalled')
            name = ready[0]
            print(json.dumps({'event': 'compile', 'module': name}), flush=True)
            data = {r['path']: r for r in builder.file_records(manifest['data'])}
            row = builder.compile_one(name, formal, manifest['modules'][name], data, lib, out,
                                      Path(compiler_path), compiler, paths, manifest['modules'])
            require(row['status'] == 'PASS', 'Changed module failed: ' + name + ': ' + row.get('error', ''))
            records = builder.artifact_pins(lib / Path(*name.split('.')).with_suffix('.olean'))
            result['rebuilt_artifacts'][name] = records; produced[name] = records
            for record in records: watched[record['path']] = {k: record[k] for k in ('sha256', 'bytes')}
            done.add(name); pending.remove(name)
        for rel, record in sources.items(): checked(formal / rel, record)
        for path, record in watched.items(): checked(Path(path), record)
        checked(Path(compiler_path), archive.custody[compiler_path])
        result.update(status='PASS', completed=sorted(done), finished_utc=utc())
    except Exception as error:
        result.update(error=str(error), finished_utc=utc()); raise
    finally:
        write_once(out / 'BUILD_RESULT.json', result)
        print(json.dumps({'status': result['status'], 'build_result': str(out / 'BUILD_RESULT.json')}), flush=True)
    build_context(formal, out / 'BUILD_RESULT.json')


def bind(args):
    context = build_context(args.formal, args.build_result); inputs = Inputs(args.native_capsule)
    out = args.output.absolute(); require(out == out.resolve(), 'Noncanonical output'); out.mkdir(parents=True, exist_ok=False)
    report = {'schema': BINDING_SCHEMA, 'part': args.part, 'passed': False, 'started_utc': utc(),
              'build_result': str(context['run'] / 'BUILD_RESULT.json'), 'build_result_pin': context['build_result_pin'],
              'source_manifest_sha256': context['build']['manifest_sha256'], 'compiler': context['compiler'],
              'native_input_manifest_sha256': ORIGINAL_NATIVE_SHA, 'solver_calls': 0,
              'emitter': {'name': EMITTERS[args.part][0], 'sha256': EMITTERS[args.part][1]},
              'output_directory': str(out), 'LEAN_PATH': context['lean_path'], 'emission_mode': 'FRESH_EXECUTION',
              'verifier_sha256': pin(Path(__file__).resolve())['sha256']}
    command = emitter_command(args.part, context['compiler']['path'], str(context['formal']), str(out))
    report['command'] = command; start = time.monotonic()
    try:
        if args.part == 'counter': (out / 'inputs.txt').write_bytes(counter_data(inputs)[0])
        env = dict(os.environ, LEAN_PATH=context['lean_path'], LEAN_NUM_THREADS='1', PYTHONDONTWRITEBYTECODE='1')
        with (out / 'emit.log').open('xb') as log:
            if args.part == 'base':
                with (out / 'lean-base.body').open('xb') as data:
                    process = subprocess.run(command, cwd=context['formal'] / 'reproduce', env=env, stdout=data, stderr=log)
            else:
                process = subprocess.run(command, cwd=context['formal'] / 'reproduce', env=env, stdout=log, stderr=subprocess.STDOUT)
        report['exit_code'] = process.returncode; require(process.returncode == 0, 'Lean emission failed; see emit.log')
        report['comparison'] = compare(args.part, out, inputs)
        verify_live_context(context); inputs.unchanged()
        report['files'] = {str(p.relative_to(out)): pin(p) for p in sorted(out.rglob('*')) if p.is_file()}
        report['input_files'] = inputs.used
        report.update(passed=True, finished_utc=utc(), elapsed_seconds=time.monotonic() - start)
    except Exception as error:
        report.update(error=str(error), finished_utc=utc(), elapsed_seconds=time.monotonic() - start)
        raise
    finally:
        write_once(out / 'RESULT.json', report)
        print(json.dumps({'part': args.part, 'passed': report['passed'], 'report': str(out / 'RESULT.json')}), flush=True)


def emission_reuse(context, part):
    """Authenticate unchanged execution inputs at the accepted custody boundary."""
    require('baseline_archive' in context, 'Emission reuse requires an authenticated composite build')
    archive = context['baseline_archive']; baseline = archive.json(archive.manifest['build_result'])
    receipt_origin = archive.manifest['bindings'][part]; receipt = archive.json(receipt_origin)
    require(receipt['passed'] is True and receipt['build_result'] == archive.manifest['build_result']
            and receipt['build_result_sha256'] == historical.pin(archive.get(archive.manifest['build_result']))['sha256']
            and receipt['compiler_sha256'] == context['compiler']['sha256'], 'Wrong accepted emission provenance')
    emitter_origin = str(archive.formal / 'reproduce' / EMITTERS[part][0])
    old_emitter = archive.get(emitter_origin)
    require(pin(old_emitter)['sha256'] == EMITTERS[part][1], 'Accepted emitter differs')
    compiler = context['compiler']['path']; folder = str(PurePosixPath(receipt_origin).parent)
    expected = ['/usr/bin/nice', '-n', '10', *emitter_command(part, compiler, str(archive.formal), folder)]
    command = receipt['steps'][0]['command'] if part == 'balance' else receipt['command']
    exit_code = receipt['steps'][0]['exit_code'] if part == 'balance' else receipt['exit_code']
    require(command == expected and exit_code == 0, 'Accepted compiler/emitter/options differ')
    manifest = read_json(context['formal'] / 'SOURCE_MANIFEST.json')
    old_rows = {row['module']: row for row in baseline['modules']}; closure = set(); stack = historical.imports_of(old_emitter.read_text())
    while stack:
        name = stack.pop()
        if name in closure: continue
        require(name in manifest['modules'] and name in context['build']['reused_modules'],
                'Emitter imports a changed or unaccepted project module')
        closure.add(name)
        stack.extend(d for d in manifest['modules'][name]['imports'] if d in manifest['modules'])
    records = {}
    for name in sorted(closure):
        prior = old_rows[name]
        require(manifest['modules'][name]['sha256'] == baseline['sources'][name]['sha256'], 'Emitter dependency source changed')
        old_stem = prior['artifacts'][0]['path'][:-len('.olean')]
        new_stem = context['logical_run'] + '/lib/' + name.replace('.', '/')
        for record in prior['artifacts']:
            path = new_stem + record['path'][len(old_stem):]; wanted = archive.custody[record['path']]
            require(context['artifacts'].get(path) == wanted, 'Emitter dependency artifact/companion changed')
            records[path] = wanted
        for imported in prior['imports'].values():
            for record in imported:
                path = record['path']
                if not path.startswith(baseline['lean_path'].split(os.pathsep)[0] + '/'):
                    require(context['artifacts'].get(path) == archive.custody[path], 'Recorded external import changed')
                    records[path] = archive.custody[path]
    require(context['compiler']['path'] == baseline['modules'][-1]['command'][3]
            and context['compiler']['sha256'] == baseline['compiler_sha256'], 'Emitter compiler changed')
    original_files = accepted_emission_files(context, part)
    return {'original_binding_receipt': receipt_origin, 'original_binding_receipt_pin': pin(archive.get(receipt_origin)),
            'original_build_result': archive.manifest['build_result'], 'command': command,
            'project_modules': sorted(closure), 'recorded_artifact_count': len(records),
            'recorded_artifact_sha256': digest(json.dumps(records, sort_keys=True, separators=(',', ':')).encode()),
            'emission_files': {rel: item['pin'] for rel, item in original_files.items()},
            'scope': 'Identical compiler, emitter/options, transitive project artifacts and companions, and all originally recorded external import artifacts; locked dependency trust unchanged.'}


def accepted_emission_files(context, part):
    archive = context['baseline_archive']; folder = PurePosixPath(archive.manifest['bindings'][part]).parent
    names = {'base': ['lean-base.body', 'emit.log'],
             'marked': ['units/abd.tsv', 'units/e.tsv', 'units/entrances.tsv', 'emit.log'],
             'counter': ['inputs.txt', 'lean-counters.cnf', 'emit.log'],
             'balance': ['prefixes/' + x + '.cnf' for x in
                         ['C2_ROOT_' + o for o in ('UU', 'UT', 'TU', 'TT')] + ['C1_FIVE_' + o for o in ('UU', 'UT', 'TT')]]}
    result = {rel: {'origin': str(folder / rel), 'pin': pin(archive.get(str(folder / rel)))} for rel in names[part]}
    if part == 'balance':
        original = str(folder / 'prefix-emission.log'); result['emit.log'] = {'origin': original, 'pin': pin(archive.get(original))}
    return result


def rebind(args):
    context = build_context(args.formal, args.build_result); inputs = Inputs(args.native_capsule)
    reuse = emission_reuse(context, args.part); archive = context['baseline_archive']
    out = args.output.absolute(); require(out == out.resolve(), 'Noncanonical rebind output'); out.mkdir(parents=True, exist_ok=False)
    for rel, item in accepted_emission_files(context, args.part).items():
        copy_checked(archive.get(item['origin']), out / rel, item['pin'])
    comparison = compare(args.part, out, inputs); verify_live_context(context); inputs.unchanged()
    report = {'schema': BINDING_SCHEMA, 'part': args.part, 'passed': True, 'checked_utc': utc(),
              'build_result': str(context['run'] / 'BUILD_RESULT.json'), 'build_result_pin': context['build_result_pin'],
              'source_manifest_sha256': context['build']['manifest_sha256'], 'compiler': context['compiler'],
              'native_input_manifest_sha256': ORIGINAL_NATIVE_SHA, 'solver_calls': 0, 'new_lean_calls': 0,
              'emitter': {'name': EMITTERS[args.part][0], 'sha256': EMITTERS[args.part][1]},
              'output_directory': str(out), 'LEAN_PATH': context['lean_path'],
              'emission_mode': 'REUSED_IDENTICAL_RECORDED_RUNTIME', 'reuse': reuse,
              'verifier_sha256': pin(Path(__file__).resolve())['sha256'], 'command': reuse['command'], 'exit_code': 0,
              'comparison': comparison, 'input_files': inputs.used,
              'files': {str(p.relative_to(out)): pin(p) for p in sorted(out.rglob('*')) if p.is_file()}}
    write_once(out / 'RESULT.json', report)
    print(json.dumps({'part': args.part, 'passed': True, 'mode': report['emission_mode'], 'report': str(out / 'RESULT.json')}), flush=True)


def binding_context(part, folder, context, inputs, logical_folder, verifier_sha):
    report_path = regular(folder / 'RESULT.json'); report = read_json(report_path)
    require(report['schema'] == BINDING_SCHEMA and report['part'] == part and report['passed'] is True
            and report['exit_code'] == 0 and report['solver_calls'] == 0, 'Failed or wrong input binding')
    require(report['build_result'] == context['logical_run'] + '/BUILD_RESULT.json'
            and report['build_result_pin'] == context['build_result_pin']
            and report['source_manifest_sha256'] == context['build']['manifest_sha256']
            and report['compiler'] == context['compiler'] and report['LEAN_PATH'] == context['lean_path']
            and report['verifier_sha256'] == verifier_sha, 'Binding belongs to another build or verifier')
    require(report['emitter'] == {'name': EMITTERS[part][0], 'sha256': EMITTERS[part][1]}
            and report['native_input_manifest_sha256'] == ORIGINAL_NATIVE_SHA
            and report['output_directory'] == logical_folder,
            'Wrong emission command/authority')
    if report['emission_mode'] == 'FRESH_EXECUTION':
        require(report['command'] == emitter_command(part, context['compiler']['path'], context['logical_formal'], logical_folder),
                'Wrong fresh emission command')
    else:
        require(report['emission_mode'] == 'REUSED_IDENTICAL_RECORDED_RUNTIME' and report['new_lean_calls'] == 0,
                'Unknown emission mode')
        reuse = emission_reuse(context, part)
        require(report['reuse'] == reuse and report['command'] == reuse['command'], 'Emission reuse identity changed')
        require(report['files'] == reuse['emission_files'], 'Reused output bytes differ from original accepted emission')
    files = {'RESULT.json': pin(report_path)}
    for rel, record in report['files'].items():
        member(rel); checked(folder / rel, record); files[rel] = record
    actual = {str(p.relative_to(folder)) for p in folder.rglob('*') if p.is_file()}
    require(actual == set(files), 'Unexpected or missing binding file')
    for rel, record in report['input_files'].items():
        require(inputs.manifest['files'].get(rel) == record, 'Wrong binding input pin'); inputs.path(rel)
    require(report['comparison'] == compare(part, folder, inputs), 'Binding receipt disagrees with retained emissions')
    return report, files


def copy_checked(source, destination, record):
    checked(source, record); destination.parent.mkdir(parents=True, exist_ok=True)
    require(not destination.exists(), 'Refusing existing capsule file')
    shutil.copyfile(source, destination); checked(destination, record)


def prepare(args):
    context = build_context(args.formal, args.build_result); inputs = Inputs(args.native_capsule)
    bindings = args.bindings.resolve(strict=True); out = args.output.absolute()
    require(out == out.resolve(), 'Noncanonical capsule destination'); out.mkdir(parents=True, exist_ok=False)
    verifier = Path(__file__).resolve(); verifier_pin = pin(verifier); reports = {}; files = {}; binding_origins = {}
    def retain(src, rel, record):
        member(rel); copy_checked(src, out / rel, record); files[rel] = record
    for part in PARTS:
        folder = bindings / part
        report, records = binding_context(part, folder, context, inputs, str(folder), verifier_pin['sha256'])
        reports[part] = report['comparison']; binding_origins[part] = str(folder)
        for rel, record in records.items(): retain(folder / rel, 'bindings/' + part + '/' + rel, record)
    for rel, record in context['source_files'].items(): retain(context['formal'] / rel, 'formal/' + rel, record)
    for rel, record in context['build_files'].items(): retain(context['run'] / rel, 'build/' + rel, record)
    if 'baseline_archive' in context:
        archive = context['baseline_archive']
        for rel, record in archive.files.items(): retain(archive.root / rel, 'build/baseline/' + rel, record)
        retain(archive.root / 'FORMAL_RELEASE.json', 'build/baseline/FORMAL_RELEASE.json', pin(archive.root / 'FORMAL_RELEASE.json'))
    retain(inputs.authority, 'inputs/NATIVE_RELEASE.json', pin(inputs.authority))
    for rel, record in inputs.used.items(): retain(inputs.root / rel, 'inputs/' + rel, record)
    retain(verifier, 'tools/publication_formal_evidence.py', verifier_pin)
    helper = Path(historical.__file__).resolve(); retain(helper, 'tools/formal_evidence.py', pin(helper))
    verify_live_context(context); inputs.unchanged()
    manifest = {'schema': SCHEMA, 'created_utc': utc(), 'total_formulas': TOTAL, 'selected_modules': MODULE_COUNT,
                'conditional_reduction_only': True, 'solver_calls': 0, 'trust': TRUST,
                'source_manifest_sha256': context['build']['manifest_sha256'], 'files': files,
                'origins': {'formal': str(context['formal']), 'build': str(context['run']), 'bindings': binding_origins},
                'bindings': reports, 'verifier_sha256': verifier_pin['sha256'],
                'build_mode': 'authenticated_composite' if 'baseline_archive' in context else 'fresh_all_selected_modules'}
    write_once(out / 'FORMAL_PUBLICATION.json', manifest)
    result = verify(out, pin(out / 'FORMAL_PUBLICATION.json')['sha256'])
    print(json.dumps(result, indent=2), flush=True)


def verify(capsule, manifest_sha256):
    capsule = Path(capsule).resolve(strict=True)
    path = checked(capsule / 'FORMAL_PUBLICATION.json', {'sha256': manifest_sha256})
    manifest = read_json(path)
    require(manifest['schema'] == SCHEMA and manifest['total_formulas'] == TOTAL
            and manifest['selected_modules'] == MODULE_COUNT and manifest['conditional_reduction_only'] is True
            and manifest['solver_calls'] == 0 and manifest['trust'] == TRUST, 'Wrong formal publication policy')
    require(manifest['verifier_sha256'] == pin(Path(__file__).resolve())['sha256'], 'Wrong publication verifier version')
    require(manifest['files'].get('tools/publication_formal_evidence.py') == pin(Path(__file__).resolve())
            and manifest['files'].get('tools/formal_evidence.py') == pin(Path(historical.__file__).resolve()),
            'Current verifier/helper differs from retained source')
    for rel, record in manifest['files'].items(): member(rel); checked(capsule / rel, record)
    require(not any(p.is_symlink() for p in capsule.rglob('*')), 'Linked capsule member')
    require({str(p.relative_to(capsule)) for p in capsule.rglob('*') if p.is_file()} ==
            set(manifest['files']) | {'FORMAL_PUBLICATION.json'}, 'Extra or missing capsule member')
    origins = manifest['origins']
    context = build_context(capsule / 'formal', capsule / 'build/BUILD_RESULT.json',
                            logical_formal=origins['formal'], logical_run=origins['build'], live=False)
    require(manifest['build_mode'] == ('authenticated_composite' if 'baseline_archive' in context else 'fresh_all_selected_modules'),
            'Misrepresented build mode')
    require(manifest['source_manifest_sha256'] == context['build']['manifest_sha256'], 'Source manifest mismatch')
    inputs = Inputs(capsule / 'inputs'); reports = {}
    require(set(origins['bindings']) == set(PARTS), 'Missing binding origin')
    for part in PARTS:
        report, _ = binding_context(part, capsule / 'bindings' / part, context, inputs,
                                    str(origin(origins['bindings'][part])), manifest['verifier_sha256'])
        reports[part] = report['comparison']
    require(reports == manifest['bindings'], 'Formal summary differs from retained evidence')
    require(reports['marked']['formulas'] + reports['balance']['formulas'] == TOTAL, 'Wrong complete selected boundary')
    inputs.unchanged()
    return {'schema': SCHEMA, 'passed': True, 'manifest_sha256': manifest_sha256,
            'total_formulas': TOTAL, 'selected_modules': MODULE_COUNT,
            'build_mode': manifest['build_mode'],
            'conditional_reduction_only': True, 'solver_calls': 0,
            'scope': 'Portable source/build provenance and four exact-input bindings; native UNSAT checked separately.'}


def self_test():
    class Tests(unittest.TestCase):
        def test_paths(self):
            for value in ('../escape', '/absolute', 'x/../y', 'x\\y'):
                with self.assertRaises(ValueError): member(value)
        def test_relative_input(self):
            self.assertEqual(relative('inputs-e-exhaustive/manifest.json', '../base.cnf'), 'base.cnf')
            with self.assertRaises(ValueError): relative('a.json', '../../escape')
        def test_exact_command(self):
            self.assertEqual(emitter_command('base', '/lean', '/formal', '/out'),
                             ['/lean', '-j1', '--run', '/formal/reproduce/EmitBase.lean'])
            self.assertEqual(emitter_command('balance', '/lean', '/formal', '/out')[-1], '/out/prefixes')
        def test_bad_axiom(self):
            with self.assertRaises(ValueError): historical.audit_axioms("'x' depends on axioms: [sorryAx]")
            with self.assertRaises(ValueError): historical.audit_axioms("'x' depends on axioms: [extraAxiom]")
    result = unittest.TextTestRunner().run(unittest.defaultTestLoader.loadTestsFromTestCase(Tests))
    require(result.wasSuccessful(), 'Self tests failed')


def main():
    parser = argparse.ArgumentParser(description=__doc__); sub = parser.add_subparsers(dest='mode', required=True)
    for name in ('bind', 'rebind', 'prepare'):
        p = sub.add_parser(name); p.add_argument('--formal', type=Path, required=True)
        p.add_argument('--build-result', type=Path, required=True); p.add_argument('--native-capsule', type=Path, required=True)
        p.add_argument('--output', type=Path, required=True)
        if name in ('bind', 'rebind'): p.add_argument('--part', choices=PARTS, required=True)
        else: p.add_argument('--bindings', type=Path, required=True)
    p = sub.add_parser('verify'); p.add_argument('--capsule', type=Path, required=True); p.add_argument('--manifest-sha256', required=True)
    p = sub.add_parser('composite-build'); p.add_argument('--formal', type=Path, required=True)
    p.add_argument('--baseline-capsule', type=Path, required=True); p.add_argument('--output', type=Path, required=True)
    sub.add_parser('self-test'); args = parser.parse_args()
    require(not sys.flags.optimize, 'Python -O is forbidden')
    if args.mode == 'bind': bind(args)
    elif args.mode == 'rebind': rebind(args)
    elif args.mode == 'prepare': prepare(args)
    elif args.mode == 'composite-build': composite_build(args)
    elif args.mode == 'verify': print(json.dumps(verify(args.capsule, args.manifest_sha256), indent=2))
    else: self_test()


if __name__ == '__main__':
    try: main()
    except (ValueError, OSError, KeyError, TypeError, subprocess.SubprocessError) as error:
        print('FAIL: ' + str(error), file=sys.stderr); raise SystemExit(1)
