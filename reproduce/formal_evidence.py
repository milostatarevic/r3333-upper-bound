#!/usr/bin/env python3
"""Portable, conditional K60 formal-reduction evidence (Python standard library).

Prepare authenticates a final source build and its four complete input bindings.
Verify replays source/import, receipt and exact-emission checks using archive
members only: no old private path, compiled artifact, Lean, solver, or archived
Python program is required or executed. Native UNSAT is a separate release gate.
"""
import argparse
from collections import Counter
import datetime as dt
import hashlib
import itertools
import json
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import tempfile
import unittest
import uuid

SCHEMA = 'K60_FORMAL_RELEASE_1'
TRUST = ('Conditional formal reduction to the explicitly enumerated CNF UNSAT '
         'premise, with exact-input binding provenance. This package asserts '
         'neither native campaign completion nor checked UNSAT refutations. '
         'Archived execution receipts are provenance, not a replay of Lean.')
BASELINE_MANIFEST_SHA = 'a3b8f63435129f551e318053c4febdf915da110e4f56bea9fa7f4bdb81a7e6e6'
BASE_SHA = 'a48d929e734201beebccd8089578c229fb4cfccd16b3a7d5d9111edf39764cbe'
CATALOGUES = {
    'abd': ('inputs-abd-exhaustive/manifest.json', 56374,
            'fc94af1694ca41df160da21950f48432668afa16014540ffbec79d96ecc6c50f'),
    'e': ('inputs-e-exhaustive/manifest.json', 231168,
          '1c1fe1bbb2166d058b99a5e3ab16dfff0a81e0f802911879875ed055141cbedb'),
    'entrances': ('inputs-k60-entrances/manifest.json', 8532,
                  '4ec3d6f6871d9638a908d1d70ada2d68e1e0095cebbd8627fc0a6d0e90b1abbf'),
}
BALANCE_MANIFESTS = {
    'balance-simplification-pilot/manifest-pentagon-only.json':
        '1999e8a27e25fdf080509ca028269801e716171f10aac28c1245847974ecc84d',
    'inputs-balance-fiveguards-all/manifest.json':
        '5c39d4af5c9a65eafcfafad4db2473edc8a2529983304ab2bad9938302e3c803',
    'balance-simplified-full/manifest.json':
        '0240d89463111e4fb51d8c13fb799d16524d8e10e826ed31962788440209db19',
}
REQUIRED = {
    'UniformK60.Verification', 'UniformK60.FiniteBoundary', 'UniformK60.ExactInputs',
    'UniformK60.Entrance', 'UniformK60.CEntranceComplete', 'UniformK60.CEntranceFiniteCover',
    'UniformK60.CEntranceBridgeChecks', 'UniformK60.CommonCompleteD', 'UniformK60.CommonCompleteE',
    'UniformK60.BalancedEncodingBalance', 'UniformK60.BalancedHostBraceCover',
    'UniformK60.BalancedEncodingBraces', 'UniformK60.BalancedEncodingAllFive',
    'UniformK60.BalancedEncodingData', 'UniformK60.BalancedEncodingSoundness',
    'UniformK60.SequentialCounter', 'UniformK60.CoreCounts', 'UniformK61.CommonUnitCache',
}
AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
DIGEST = re.compile(r'[0-9a-f]{64}\Z')
MODULE = re.compile(r'[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*\Z')


def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def pin(path):
    h = hashlib.sha256(); size = 0
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1 << 20), b''):
            h.update(block); size += len(block)
    return {'sha256': h.hexdigest(), 'bytes': size}


def read_json(path):
    def pairs(items):
        value = {}
        for key, item in items:
            require(key not in value, 'Duplicate JSON key: ' + key)
            value[key] = item
        return value
    return json.loads(Path(path).read_bytes(), object_pairs_hook=pairs,
                      parse_constant=lambda x: (_ for _ in ()).throw(ValueError('Nonfinite JSON: ' + x)))


def safe_member(value):
    require(isinstance(value, str) and value and '\\' not in value and '\x00' not in value,
            'Invalid archive member')
    p = PurePosixPath(value)
    require(not p.is_absolute() and str(p) == value and
            all(x not in ('', '.', '..') and ':' not in x for x in p.parts),
            'Unsafe archive member: ' + value)
    return p


def absolute_origin(value):
    require(isinstance(value, str) and '\\' not in value and '\x00' not in value,
            'Invalid original path')
    p = PurePosixPath(value)
    require(p.is_absolute() and str(p) == value and '..' not in p.parts,
            'Noncanonical original path: ' + value)
    return p


def relative_origin(parent, value):
    """Resolve a recorded relative reference; output members themselves stay canonical."""
    require(isinstance(value, str) and '\\' not in value and '\x00' not in value,
            'Invalid recorded relative reference')
    if PurePosixPath(value).is_absolute():
        return absolute_origin(value)
    parts = list(absolute_origin(str(parent)).parts)
    for part in PurePosixPath(value).parts:
        if part == '..':
            require(len(parts) > 1, 'Recorded reference escapes filesystem root')
            parts.pop()
        elif part != '.':
            parts.append(part)
    return absolute_origin(str(PurePosixPath(*parts)))


def check_pin(record):
    require(isinstance(record, dict) and DIGEST.fullmatch(record.get('sha256', '')),
            'Malformed SHA256 pin')
    if 'bytes' in record:
        require(type(record['bytes']) is int and record['bytes'] >= 0, 'Malformed byte count')


class Store:
    """One explicit original workspace root; no basename or alternate-root searching."""
    def __init__(self, workspace):
        self.workspace = absolute_origin(str(workspace))
        self.formal = self.workspace / 'k60-lean'
        self.baseline = self.workspace / 'r3333-upper-bound/formal'
        self.pilot = self.workspace / 'k60-pilot'
        self.used = set()
        self.used_custody = set()

    def member(self, origin):
        p = absolute_origin(str(origin))
        try:
            rel = p.relative_to(self.workspace)
        except ValueError as e:
            raise ValueError('Original file escapes declared workspace: ' + str(p)) from e
        require(str(rel) != '.', 'Expected a file, not the workspace root')
        return str(safe_member('workspace/' + str(rel)))

    def checked(self, origin, expected):
        check_pin(expected)
        path = self.get(str(origin)); actual = pin(path)
        require(actual['sha256'] == expected['sha256'] and
                ('bytes' not in expected or actual['bytes'] == expected['bytes']),
                'Missing or changed file: ' + str(origin))
        return path

    def json(self, origin, expected=None):
        return read_json(self.checked(origin, expected) if expected else self.get(str(origin)))


class Collector(Store):
    def __init__(self, workspace, output):
        super().__init__(workspace)
        self.output = Path(output); self.files = {}; self.watched = {}; self.custody = {}

    def get(self, origin):
        member = self.member(origin); self.used.add(member)
        if member not in self.files:
            source = Path(origin)
            require(source.is_file() and not source.is_symlink() and source.resolve() == source,
                    'Source must be a regular unlinked workspace file: ' + origin)
            before = pin(source)
            target = self.output / member; target.parent.mkdir(parents=True, exist_ok=True)
            with source.open('rb') as inp, target.open('xb') as out:
                shutil.copyfileobj(inp, out, 1 << 20)
            require(pin(target) == before == pin(source), 'Source changed while copying: ' + origin)
            self.files[member] = before; self.watched[origin] = before
        return self.output / member

    def artifact(self, record):
        """Authenticate locally, retain only the unchanged raw custody record."""
        check_pin(record); origin = str(absolute_origin(record['path']))
        if origin in self.custody:
            old = self.custody[origin]
            require(old['sha256'] == record['sha256'] and
                    ('bytes' not in record or old['bytes'] == record['bytes']), 'Conflicting artifact pin')
            self.used_custody.add(origin)
            return
        actual = pin(origin)
        require(actual['sha256'] == record['sha256'] and
                ('bytes' not in record or actual['bytes'] == record['bytes']),
                'Changed live build artifact/compiler: ' + origin)
        require(origin not in self.custody or self.custody[origin] == actual, 'Conflicting artifact pin')
        self.custody[origin] = actual
        self.used_custody.add(origin)

    def unchanged(self):
        for origin, expected in self.watched.items():
            require(pin(origin) == expected, 'Source changed during preparation: ' + origin)
        for origin, expected in self.custody.items():
            require(pin(origin) == expected, 'Build artifact changed during preparation: ' + origin)


class Archive(Store):
    def __init__(self, root, expected_sha256):
        require(DIGEST.fullmatch(expected_sha256 or ''), 'External manifest SHA256 is required')
        raw_root = Path(root)
        require(not raw_root.is_symlink() and raw_root.resolve() == raw_root.absolute(),
                'Linked archive root forbidden')
        self.root = raw_root.resolve()
        manifest_path = self.root / 'FORMAL_RELEASE.json'
        require(manifest_path.is_file() and not manifest_path.is_symlink(), 'Missing regular formal manifest')
        require(pin(manifest_path)['sha256'] == expected_sha256, 'Formal manifest hash mismatch')
        self.manifest = read_json(manifest_path)
        require(self.manifest.get('schema') == SCHEMA, 'Wrong formal capsule schema')
        super().__init__(self.manifest['origins']['workspace'])
        self.files = self.manifest['files']; self.custody = self.manifest['live_artifact_custody']
        require(isinstance(self.files, dict) and isinstance(self.custody, dict), 'Malformed file/custody map')
        for member, expected in self.files.items():
            check_pin(expected); require(set(expected) == {'sha256', 'bytes'}, 'Unexpected pin fields')
            require(pin(self.path(member)) == expected, 'Changed archive member: ' + member)
        actual = set()
        for p in self.root.rglob('*'):
            require(not p.is_symlink(), 'Archive symlink forbidden')
            if p.is_file():
                actual.add(p.relative_to(self.root).as_posix())
            else:
                require(p.is_dir(), 'Nonregular archive member')
        require(actual == set(self.files) | {'FORMAL_RELEASE.json'}, 'Missing or unexpected archive files')

    def path(self, member):
        p = self.root
        for part in safe_member(member).parts:
            p /= part; require(not p.is_symlink(), 'Archive symlink forbidden')
        require(p.is_file(), 'Missing regular archive member: ' + member)
        return p

    def get(self, origin):
        member = self.member(origin); self.used.add(member)
        require(member in self.files, 'Unpinned archived dependency: ' + member)
        return self.path(member)

    def artifact(self, record):
        check_pin(record); origin = str(absolute_origin(record['path']))
        require(origin in self.custody, 'Missing recorded live artifact custody')
        item = self.custody[origin]; check_pin(item)
        require(item['sha256'] == record['sha256'] and
                ('bytes' not in record or item['bytes'] == record['bytes']), 'Conflicting artifact custody')
        self.used_custody.add(origin)


def lean_code(text, keep_strings=False):
    """Remove nested comments, optionally preserving string literals in place."""
    result = []; i = 0; depth = 0; quoted = False
    while i < len(text):
        if depth:
            if text.startswith('/-', i): depth += 1; result.extend('  '); i += 2
            elif text.startswith('-/', i): depth -= 1; result.extend('  '); i += 2
            else: result.append('\n' if text[i] == '\n' else ' '); i += 1
        elif quoted:
            if text[i] == '\\' and i + 1 < len(text):
                result.extend(text[i:i+2] if keep_strings else '  '); i += 2
            else:
                if text[i] == '"': quoted = False
                result.append(text[i] if keep_strings else '\n' if text[i] == '\n' else ' '); i += 1
        elif text.startswith('--', i):
            j = text.find('\n', i); j = len(text) if j < 0 else j
            result.extend(' ' * (j - i)); i = j
        elif text.startswith('/-', i): depth = 1; result.extend('  '); i += 2
        elif text[i] == '"': quoted = True; result.append('"' if keep_strings else ' '); i += 1
        else: result.append(text[i]); i += 1
    require(depth == 0 and not quoted, 'Unterminated Lean comment/string')
    return ''.join(result)


def embedded_paths(text):
    """Read actual include_str arguments, ignoring appearances inside comments/strings."""
    code = lean_code(text); visible = lean_code(text, keep_strings=True); paths = []
    for match in re.finditer(r'\binclude_str\b', code):
        argument = re.match(r'\s*"([^"\n\\]+)"', visible[match.end():])
        require(argument is not None, 'Unsupported embedded-data argument')
        paths.append(argument[1])
    return paths


def baseline_input_records(store, baseline):
    require(len(baseline['files']) == 5 and len(baseline['data']) == 110,
            'Wrong accepted baseline control/data census')
    accepted = store.workspace/'r3333-upper-bound/publication/checks/ACCEPTED_MATH_MANIFEST.sha256'
    accepted_path = store.get(str(accepted))
    require(accepted_path.read_text().strip() == BASELINE_MANIFEST_SHA,
            'Accepted mathematical manifest identifies a different baseline')
    expected = [{'path':str(store.baseline/'SOURCE_MANIFEST.json'),'sha256':BASELINE_MANIFEST_SHA},
                {'path':str(accepted),'sha256':pin(accepted_path)['sha256']}]
    data_pins = {}
    for row in baseline['files'] + baseline['data']:
        origin = store.baseline/safe_member(row['path']); store.checked(origin,row)
        entry = {'path':str(origin),'sha256':row['sha256']}
        require(str(origin) not in data_pins, 'Duplicate accepted baseline input')
        data_pins[str(origin)] = entry; expected.append(entry)
    require(len(expected) == 117, 'Incomplete baseline input closure')
    return expected,data_pins


def embedded_records(source_origin, text, data_pins):
    expected = []
    for relative in embedded_paths(text):
        origin = str(relative_origin(absolute_origin(str(source_origin)).parent,relative))
        require(origin in data_pins, 'Unpinned embedded-data file: ' + origin)
        expected.append(data_pins[origin])
    return expected


def check_embedded_records(source_origin, text, data_pins, recorded):
    expected = embedded_records(source_origin,text,data_pins)
    require(recorded == expected, 'Per-module embedded-data custody differs from include_str dependencies')
    return expected


def imports_of(text):
    imports = []
    for line in lean_code(text).splitlines():
        match = re.match(r'^\s*(?:public\s+)?import\s+(.*)$', line)
        if match:
            names = match[1].split()
            require(names and all(MODULE.fullmatch(x) for x in names), 'Unsupported import syntax')
            imports.extend(names)
    require(len(imports) == len(set(imports)), 'Duplicate direct import')
    return imports


def selected_closure(target, texts, baseline_modules):
    found = set(); active = set()
    project_roots = {'UniformK60'} | {name.split('.')[0] for name in baseline_modules}
    def visit(name):
        if name in found: return
        require(name not in active, 'Project import cycle')
        require(name in texts, 'Omitted project module: ' + name)
        active.add(name)
        for dep in imports_of(texts[name]):
            if dep.split('.')[0] in project_roots:
                require(dep.startswith('UniformK60.') or dep in baseline_modules,
                        'Unregistered baseline project module: ' + dep)
                visit(dep)
        active.remove(name); found.add(name)
    visit(target)
    require(found == set(texts), 'Build has omitted or unrelated project source modules')
    return found


def declaration(text, name, expected):
    code = lean_code(text)
    matches = re.findall(r'\b(?:theorem|def|abbrev)\s+' + re.escape(name) + r'\b(.*?)\s*:=', code, re.S)
    require(len(matches) == 1, 'Missing or ambiguous declaration: ' + name)
    compact = lambda x: re.sub(r'\s+', '', x)
    require(compact(matches[0]) == compact(expected), 'Wrong theorem/definition signature: ' + name)


def audit_signatures(texts):
    declaration(texts['UniformK60.FiniteBoundary'], 'ramsey60_of_exact_unsat',
                '(h : ExactInputs.AllUnsat) : ∀ c : Host,¬NoMonochromaticTriangle c')
    declaration(texts['UniformK60.CEntranceComplete'], 'no_entrance_of_all_unsat',
                '(unsat : ∀ k : CEntranceFormula.Case,∀ v : DenseCounter.Valuation, '
                '¬DenseCounter.FormulaSat v (CEntranceFormula.formula k)) '
                '(c : Host) (hc : NoMonochromaticTriangle c) : ¬CEntranceWitness c')
    declaration(texts['UniformK60.Profiles'], 'Host', '')
    require(re.search(r'\babbrev\s+Host\s*:=\s*EdgeColoring\s*\(Fin\s+60\)\s+FourColor\b',
                      lean_code(texts['UniformK60.Profiles'])), 'Wrong physical host type')
    code = re.sub(r'\s+', '', lean_code(texts['UniformK60.ExactInputs']))
    require('defAllUnsat:Prop:=∀k:Case,∀v:DenseCounter.Valuation,¬DenseCounter.FormulaSatv(formulak)' in code,
            'Wrong exact UNSAT proposition')
    code = re.sub(r'\s+', '', lean_code(texts['UniformK60.Entrance']))
    require('defCEntranceWitness(c:Host):Prop:=∃rootmark,(Wcroot=32∨Wcroot=31)∧mark∈Incomingcroot∧mark∉Owncroot' in code,
            'Ordinary entrance includes an extra hypothesis or has different semantics')


def audit_axioms(log):
    require('sorryAx' not in log and "declaration uses 'sorry'" not in log, 'Unproved declaration in build log')
    for raw in re.findall(r'depends on axioms:\s*\[([^]]*)\]', log):
        require({x.strip() for x in raw.split(',') if x.strip()} <= AXIOMS, 'Nonstandard theorem axiom')


def inspect_build(store, build_origin):
    build_origin = absolute_origin(str(build_origin)); directory = build_origin.parent
    require(directory.parent == store.formal / '.build' and
            re.fullmatch(r'\d{8}T\d{6}Z_[0-9a-f]{8}', directory.name) and
            build_origin.name == 'BUILD_RESULT.json', 'Final fresh build receipt required; development receipts rejected')
    build_path = store.get(str(build_origin)); build = read_json(build_path)
    require(build.get('passed') is True and build.get('target') == 'UniformK60.Verification',
            'Successful final Verification build required')
    require(REQUIRED <= set(build.get('sources', {})), 'Initial/development or incomplete theorem build rejected')
    require('version 4.32.1,' in build['compiler'], 'Unexpected Lean version')
    baseline_origin = store.baseline / 'SOURCE_MANIFEST.json'
    baseline = store.json(baseline_origin, {'sha256': BASELINE_MANIFEST_SHA})
    expected_inputs,data_pins = baseline_input_records(store,baseline)
    require(build.get('baseline_inputs') == expected_inputs,
            'Build lacks the exact accepted baseline manifest/control/data custody')
    lake = store.json(store.baseline / 'lake-manifest.json')
    expected_packages = {x['name']: x['rev'] for x in lake['packages']}
    observed_packages = {x['name']: x['revision'] for x in build['packages']}
    require(len(observed_packages) == len(build['packages']) and observed_packages == expected_packages,
            'Missing or changed pinned package revisions')
    require(store.get(str(store.baseline / 'lean-toolchain')).read_text().strip() == 'leanprover/lean4:v4.32.1',
            'Toolchain configuration mismatch')
    for key, expected in [('builder', store.formal / 'build.py'),
                          ('source_audit', store.workspace / 'r3333-upper-bound/scripts/check_lean_sources.py')]:
        record = build[key]; require(record['path'] == str(expected), 'Noncanonical build-control source')
        store.checked(expected, record)
    texts = {}
    for name, row in build['sources'].items():
        require(MODULE.fullmatch(name), 'Invalid project module name')
        path = (store.formal if name.startswith('UniformK60.') else store.baseline) / 'src' / (name.replace('.', '/') + '.lean')
        require(row['path'] == str(path), 'Noncanonical source path: ' + name)
        if not name.startswith('UniformK60.'):
            require(name in baseline['modules'] and row['sha256'] == baseline['modules'][name]['sha256'],
                    'Baseline mathematical source changed: ' + name)
        text = store.checked(path, row).read_text(); texts[name] = text
        if not name.startswith('UniformK60.'):
            require(imports_of(text) == baseline['modules'][name]['imports'],
                    'Baseline source import declarations differ from accepted manifest')
        code = lean_code(text)
        require(not re.search(r'\b(sorry|admit|axiom|native_decide|sorryAx)\b', code), 'Proof escape in source')
        if name.startswith('UniformK60.'):
            require(not re.search(r'\b(unsafe|partial|implemented_by|extern|ofReduceBool|ofReduceNat|trustCompiler)\b|#eval\b|\brun_elab\b|debug\.skipKernelTC', code),
                    'Unreviewed proof execution escape in K60 source')
            require('include_str' not in code, 'New K60 external data needs an explicit authenticated data rule')
    selected_closure(build['target'], texts, baseline['modules']); audit_signatures(texts)
    modules = build['modules']; names = [x['module'] for x in modules]
    require(len(names) == len(set(names)) and set(names) == set(texts) and names[-1] == build['target'],
            'Missing, duplicate, or extraneous module execution receipts')
    compiler = absolute_origin(modules[-1]['command'][3])
    store.artifact({'path': str(compiler), 'sha256': build['compiler_sha256']})
    roots = [absolute_origin(x) for x in build['lean_path'].split(':')]
    require(roots and roots[0] == directory / 'lib', 'Build did not prioritize its fresh project artifact root')
    seen = {}; log_texts = {}
    for row in modules:
        name = row['module']; source = build['sources'][name]
        output = directory / 'lib' / (name.replace('.', '/') + '.olean')
        expected_cmd = ['/usr/bin/nice', '-n', '10', str(compiler), '-j1', '-o', str(output), source['path']]
        require(row['exit_code'] == 0 and row['command'] == expected_cmd, 'Invalid module compile command/outcome')
        require(row['log'] == str(directory / (name + '.log')), 'Noncanonical build log')
        log = store.checked(row['log'], {'sha256': row['log_sha256']}).read_text()
        audit_axioms(log); log_texts[name] = log
        imports = imports_of(texts[name])
        require(set(row['imports']) == set(imports), 'Import custody differs from source: ' + name)
        expected_data = check_embedded_records(source['path'],texts[name],data_pins,row.get('embedded_data'))
        for data in expected_data: store.checked(data['path'],data)
        for dep, records in row['imports'].items():
            if dep in texts:
                require(dep in seen and records == seen[dep], 'Unbuilt/stale project import: ' + dep)
            else:
                require(records and any(records[0]['path'] == str(root / (dep.replace('.', '/') + '.olean'))
                                        for root in roots[1:]), 'External import escapes declared library roots')
                first = absolute_origin(records[0]['path'])
                allowed_imports = {str(first), str(first)+'.private', str(first)+'.server', str(first.with_suffix('.ir'))}
                require(len({x['path'] for x in records}) == len(records) and
                        all(x['path'] in allowed_imports for x in records), 'Invalid external import sidecar census')
            for record in records: store.artifact(record)
        records = row['artifacts']; allowed = {str(output), str(output) + '.private', str(output) + '.server', str(output.with_suffix('.ir'))}
        require(records and records[0]['path'] == str(output) and
                len({x['path'] for x in records}) == len(records) and
                all(x['path'] in allowed for x in records), 'Wrong module output artifact census')
        for record in records: store.artifact(record)
        seen[name] = records
    final_log = log_texts[build['target']]
    for endpoint in ['UniformK60.ramsey60_of_exact_unsat', 'UniformK60.CEntranceComplete.no_entrance_of_all_unsat']:
        reports = re.findall(r"'" + re.escape(endpoint) + r"' depends on axioms:\s*\[([^]]*)\]", final_log)
        require(len(reports) == 1 and {x.strip() for x in reports[0].split(',')} == AXIOMS,
                'Missing final endpoint axiom report: ' + endpoint)
        require(re.search(r'^' + re.escape(endpoint) + r'\b', final_log, re.M), 'Missing interpreted endpoint type report')
    require('ExactInputs.AllUnsat' in final_log and 'NoMonochromaticTriangle' in final_log and
            'CEntranceWitness' in final_log, 'Endpoint type report lacks its stated boundary')
    return build, {'sha256': pin(build_path)['sha256'], 'modules': len(names),
                   'target': build['target'], 'compiler_sha256': build['compiler_sha256']}


def binding_receipt(store, origin, build_origin, build, expected_emitter=None, expected_checker=None):
    origin = absolute_origin(str(origin))
    require(origin.parent.parent == store.formal / '.build' and origin.name == 'RESULT.json' and
            not origin.parent.name.startswith('.dev'), 'Final binding receipt required')
    row = store.json(origin)
    require(row.get('passed') is True and row['build_result'] == str(build_origin) and
            row['build_result_sha256'] == pin(store.get(str(build_origin)))['sha256'] and
            row['compiler_sha256'] == build['compiler_sha256'], 'Binding belongs to an incomplete/different build')
    if expected_emitter:
        emitter = store.formal / 'reproduce' / expected_emitter
        text = store.checked(emitter, {'sha256': row['emitter_sha256']}).read_text()
        require(all(not d.startswith('UniformK60.') or d in build['sources'] for d in imports_of(text)),
                'Emitter imports unbuilt K60 module')
    if expected_checker:
        store.checked(store.formal / expected_checker, {'sha256': row['checker_sha256']})
    return row


def run_command(store, command, compiler, script, arguments):
    require(command == ['/usr/bin/nice', '-n', '10', compiler, '-j1', '--run', str(script)] + list(map(str, arguments)),
            'Unexpected emission command')


def generated_base():
    def var(u, v, q): return 4 * (u * (119-u) // 2 + v-u-1) + q+1
    lines = []
    for u, v in itertools.combinations(range(60), 2):
        atoms = [var(u, v, q) for q in range(4)]
        lines.append(' '.join(map(str, atoms)) + ' 0\n')
        lines.extend(f'-{a} -{b} 0\n' for a, b in itertools.combinations(atoms, 2))
    for u, v, w in itertools.combinations(range(60), 3):
        lines.extend(f'-{var(u,v,q)} -{var(u,w,q)} -{var(v,w,q)} 0\n' for q in range(4))
    require(len(lines) == 149270, 'Internal base census failure')
    return ''.join(lines).encode()


def formula_digest(seed_cache, base_body, units):
    n = len(units)
    if n not in seed_cache:
        h = hashlib.sha256(f'p cnf 7080 {149270+n}\n'.encode()); h.update(base_body); seed_cache[n] = h
    h = seed_cache[n].copy(); h.update(''.join(f'{x} 0\n' for x in units).encode())
    return h.hexdigest()


def retain_binding_bases(store, body, e_manifest):
    """Preserve both distinct runtime paths used by the unchanged binding wrappers.

    The caller has authenticated e_manifest against the frozen E manifest pin.
    check_base.py reads its base; check_marked_inputs.py reads the entrance base.
    Equal content hashes do not make these paths interchangeable during replay.
    """
    raw = b'p cnf 7080 149270\n'+body
    require(sha(raw) == BASE_SHA, 'Independent K60 base hash mismatch')
    entrance = store.pilot/'inputs-k60-entrances/base.cnf'
    require(store.checked(entrance,{'sha256':BASE_SHA}).read_bytes() == raw,
            'Entrance base is not the complete K60 base')
    record = e_manifest['base']
    origin = relative_origin(store.pilot/'inputs-e-exhaustive',record['path'])
    require(origin == store.pilot/'inputs-e-exhaustive/base.cnf', 'Noncanonical E base runtime path')
    require(record['sha256'] == BASE_SHA and record['body_sha256'] == sha(body) and
            record['variables'] == 7080 and record['clauses'] == 149270,
            'E manifest has a different physical base')
    require(store.checked(origin,record).read_bytes() == raw, 'E base differs from the independent K60 base')
    return [str(entrance),str(origin)]


def expected_marked(store):
    expected = {}
    for family, (relative, count, digest) in CATALOGUES.items():
        origin = store.pilot / relative; manifest = store.json(origin, {'sha256': digest}); census = Counter()
        if family == 'entrances':
            rows = manifest['cases']; require(len(rows) == count and len({r['id'] for r in rows}) == count, 'Wrong entrance census')
            for row in rows: census[(row['family'], row['sha256'])] += 1
        else:
            index = manifest['hash_index']; ledger = store.checked(relative_origin(origin.parent, index['path']), index).read_bytes()
            require(len(ledger) == 34 * count, 'Incomplete marked hash ledger')
            next_ordinal = 0
            for factor in manifest['factors']:
                start, stop = factor['ordinal_start'], factor['ordinal_stop']
                require(type(start) is int and type(stop) is int and start == next_ordinal and
                        start < stop <= count and factor['case_count'] == stop-start, 'Noncontiguous marked factors')
                owner = ('E_' if family == 'e' else '') + factor['owner']
                for i in range(start, stop): census[(owner, ledger[34*i:34*i+32].hex())] += 1
                next_ordinal = stop
            require(next_ordinal == count, 'Omitted marked factors')
        require(sum(census.values()) == count, 'Marked census mismatch'); expected[family] = census
    return expected


def inspect_bindings(store, build_origin, build, origins):
    require(set(origins) == {'base', 'marked', 'counter', 'balance'}, 'All four final-build bindings required')
    compiler = build['modules'][-1]['command'][3]
    rows = {name: binding_receipt(store, origins[name], build_origin, build,
            {'base':'EmitBase.lean','marked':'EmitMarkedK60.lean','counter':'EmitCounters.lean'}.get(name),
            {'marked':'check_marked_inputs.py','counter':'check_counters.py','balance':'check_balance.py'}.get(name))
            for name in origins}
    dirs = {name: absolute_origin(origins[name]).parent for name in origins}
    for name in ['base', 'marked', 'counter']:
        require(rows[name]['exit_code'] == 0, 'Failed emission')
        store.get(str(dirs[name] / 'emit.log'))
    body = generated_base()
    e_manifest = store.json(store.pilot/CATALOGUES['e'][0],{'sha256':CATALOGUES['e'][2]})
    retain_binding_bases(store,body,e_manifest)
    base = rows['base']; emitted = store.get(str(dirs['base'] / 'lean-base.body'))
    require(emitted.read_bytes() == body and base['clauses'] == 149270 and base['bytes'] == len(body) and
            base['catalogue_sha256'] == CATALOGUES['e'][2] and base['frozen_base_sha256'] == BASE_SHA and
            base['expected_body_sha256'] == base['emitted_body_sha256'] == sha(body), 'Invalid full base binding')
    run_command(store, base['command'], compiler, store.formal/'reproduce/EmitBase.lean', [])
    expected = expected_marked(store); census_digest = hashlib.sha256(); marked = rows['marked']
    require(set(marked['families']) == set(CATALOGUES), 'Incomplete marked family binding')
    run_command(store, marked['command'], compiler, store.formal/'reproduce/EmitMarkedK60.lean', [dirs['marked']/'units'])
    for record in marked['catalogue_pins']: store.checked(record['path'], record)
    seeds = {}; marked_summary = {}
    for family, wanted in expected.items():
        origin = dirs['marked'] / 'units' / (family + '.tsv'); report = marked['families'][family]
        require(report['emitted_units'] == str(origin), 'Wrong retained marked emission path')
        path = store.checked(origin, {'sha256':report['emitted_units_sha256']})
        seen = set(); found = Counter(); owners = Counter()
        with path.open() as stream:
            for line in stream:
                parts = line.rstrip('\n').split('\t'); require(len(parts) == 3, 'Malformed marked emission')
                owner, key, text = parts
                require((owner, key) not in seen, 'Repeated emitted case index'); seen.add((owner, key))
                units = [int(x) for x in text.split(',')]
                require(units and all(0 < abs(x) <= 7080 for x in units) and len(units) == len(set(units)) and
                        not set(units) & {-x for x in units}, 'Invalid signed physical units')
                require(family == 'entrances' or units == sorted(units), 'Unsorted ABD/E units')
                digest = formula_digest(seeds, body, units); found[(owner,digest)] += 1; owners[owner] += 1
        require(found == wanted, 'Missing or altered exact marked formula occurrences: ' + family)
        require(report['passed'] is True and report['cases'] == report['expected_cases'] == sum(found.values()) and
                report['owner_counts'] == dict(owners) and report['missing_formula_occurrences'] == 0 and
                report['unexpected_formula_occurrences'] == 0 and not report['missing_sample'] and not report['unexpected_sample'],
                'Marked receipt disagrees with retained emissions')
        for (owner,digest), n in sorted(found.items()): census_digest.update(f'{family} {owner} {digest} {n}\n'.encode())
        marked_summary[family] = sum(found.values())
    manifests = {rel: store.json(store.pilot/rel, {'sha256':digest}) for rel,digest in BALANCE_MANIFESTS.items()}
    mixed = manifests['balance-simplified-full/manifest.json']; counter = rows['counter']
    require(counter['manifest_sha256'] == BALANCE_MANIFESTS['balance-simplified-full/manifest.json'] and
            counter['blocks'] == 960 and counter['prefixes'] == 4, 'Wrong counter boundary')
    counter_hash = hashlib.sha256(); inputs = []; clause_count = 0
    for prefix in mixed['prefixes']:
        raw = store.checked(store.pilot/prefix['cnf'], {'sha256':prefix['sha256']}).read_bytes()
        metadata = store.json(store.pilot/prefix['metadata'], {'sha256':prefix['metadata_sha256']})
        lines = raw.splitlines(); require(len(lines) == prefix['clauses']+1 and
            lines[0] == f'p cnf {prefix["variables"]} {prefix["clauses"]}'.encode(), 'Invalid counter source prefix')
        require(len(metadata['cardinalities']) == 240, 'Missing vertex/color counter blocks'); top = 7080
        for block in metadata['cardinalities']:
            atoms = block['literals']; require(block['relation'] == 'atmost' and block['bound'] >= 0 and
                all(type(a) is int and 0<a<=7080 for a in atoms), 'Invalid degree counter metadata')
            inputs.append(' '.join(map(str, [top,block['bound']] + atoms)))
            if block['first_aux'] is None:
                require(block['last_aux'] is None, 'Inconsistent empty counter allocation')
            else:
                require(block['first_aux'] == top+1 and block['last_aux'] >= block['first_aux'], 'Invalid counter allocation')
                top = block['last_aux']
            first, last = block['first_clause'], block['last_clause']
            require(0 < first <= last+1 <= len(lines), 'Counter clause range escapes prefix')
            counter_hash.update(f'c counter {top}\n'.encode())
            for line in lines[first:last+1]: counter_hash.update(line+b'\n'); clause_count += 1
    require(len(inputs) == 960, 'Incomplete counter block census')
    require(store.get(str(dirs['counter']/'inputs.txt')).read_bytes() == ('\n'.join(inputs)+'\n').encode(), 'Changed counter inputs')
    emitted_counter = store.get(str(dirs['counter']/'lean-counters.cnf'))
    require(counter['expected_sha256'] == counter['emitted_sha256'] == counter_hash.hexdigest() == pin(emitted_counter)['sha256'] and
            counter['ordered_clauses_compared'] == clause_count, 'Counter emission mismatch')
    for record in counter['prefix_pins']: store.checked(record['path'], record)
    run_command(store, counter['command'], compiler, store.formal/'reproduce/EmitCounters.lean',
                [dirs['counter']/'inputs.txt', dirs['counter']/'lean-counters.cnf'])
    balance = rows['balance']; require(balance['manifest_pins'] == BALANCE_MANIFESTS and balance['solver_executed'] is False,
            'Unexpected balance manifests or execution claim')
    scripts = {store.formal/'reproduce'/x for x in ['EmitBalanced.lean','EmitBalancedUnits.lean',
               'check_balanced_prefixes.py','check_balanced_units.py']}
    require(set(balance['script_pins']) == {str(x) for x in scripts}, 'Incomplete balance tool source set')
    for origin,digest in balance['script_pins'].items(): store.checked(origin, {'sha256':digest})
    expected_steps = ['prefix-emission','unit-emission','prefix-comparison','unit-comparison']
    require([x['name'] for x in balance['steps']] == expected_steps, 'Missing/extra balance execution steps')
    for step in balance['steps']:
        require(step['exit_code'] == 0 and step['log'] == str(dirs['balance']/(step['name']+'.log')), 'Invalid balance step')
        store.checked(step['log'], {'sha256':step['log_sha256']})
    run_command(store, balance['steps'][0]['command'], compiler, store.formal/'reproduce/EmitBalanced.lean', [dirs['balance']/'prefixes'])
    run_command(store, balance['steps'][1]['command'], compiler, store.formal/'reproduce/EmitBalancedUnits.lean', [dirs['balance']/'units.tsv'])
    for step, script, arg, out in [(balance['steps'][2],'check_balanced_prefixes.py','prefixes','prefix-binding.json'),
                                  (balance['steps'][3],'check_balanced_units.py','units.tsv','unit-binding.json')]:
        cmd = step['command']; absolute_origin(cmd[0])
        require(cmd[1:] == [str(store.formal/'reproduce'/script), str(dirs['balance']/arg), '--output', str(dirs['balance']/out)],
                'Unexpected comparison command')
    prefixes = store.json(dirs['balance']/'prefix-binding.json'); units_report = store.json(dirs['balance']/'unit-binding.json')
    require(prefixes == balance['prefixes'] and units_report == balance['units'], 'Changed balance component receipts')
    for report in [prefixes, units_report]:
        for origin,digest in report['source_sha256'].items(): store.checked(origin, {'sha256':digest})
    prefix_specs = [(p['id'],p,relative_origin(store.pilot/'balance-simplification-pilot',p['cnf']))
                    for p in manifests['balance-simplification-pilot/manifest-pentagon-only.json']['prefixes']]
    prefix_specs += [('C1_FIVE_'+p['owner'],p,relative_origin(store.pilot/'inputs-balance-fiveguards-all',p['cnf']))
                     for p in manifests['inputs-balance-fiveguards-all/manifest.json']['cases']]
    require(prefixes['passed'] is True and prefixes['formulas'] == 7 and len(prefixes['rows']) == 7, 'Incomplete seven-prefix binding')
    for record,(name,spec,origin) in zip(prefixes['rows'],prefix_specs):
        emitted_origin = dirs['balance']/'prefixes'/(name+'.cnf')
        require(record['id'] == name and record['emitted'] == str(emitted_origin) and record['frozen'] == str(origin) and
                record['exact_match'] is True and record['variables'] == spec['variables'] and record['clauses'] == spec['clauses'] and
                record['emitted_sha256'] == record['frozen_sha256'] == spec['sha256'], 'Prefix receipt mismatch')
        a = store.checked(emitted_origin, {'sha256':spec['sha256'],'bytes':record['bytes']})
        b = store.checked(origin, {'sha256':spec['sha256'],'bytes':record['bytes']})
        require(a.read_bytes() == b.read_bytes(), 'Unequal exact prefix bytes')
    for origin,digest in prefixes['manifest_sha256'].items(): store.checked(origin, {'sha256':digest})
    path = store.checked(dirs['balance']/'units.tsv', {'sha256':units_report['emitted_sha256']})
    cases = mixed['cases']; require(len(cases) == 720, 'Wrong mixed case census')
    seeds = {}; ordered = hashlib.sha256(); total_units = 0; n = 0
    prefix_by_id = {p['id']:p for p in mixed['prefixes']}
    with path.open() as stream:
        for index,line in enumerate(stream):
            require(index < 720, 'Extra brace emission'); r,m,*units = map(int,line.split()); case = cases[index]
            require((r,m) == divmod(index,12) and r == case['projected_row_index'] and units == case['unit_literals'], 'Brace fact mismatch')
            prefix = prefix_by_id[case['baseline_id']]; key = (case['baseline_id'],case['clauses'])
            require(case['clauses'] == prefix['clauses']+len(units) and case['variables'] == prefix['variables'], 'Brace full formula census mismatch')
            if key not in seeds:
                raw = store.checked(store.pilot/prefix['cnf'], {'sha256':prefix['sha256']}).read_bytes()
                seeds[key] = hashlib.sha256(f'p cnf {case["variables"]} {case["clauses"]}\n'.encode()+raw.split(b'\n',1)[1])
            h = seeds[key].copy(); h.update(''.join(f'{u} 0\n' for u in units).encode())
            require(h.hexdigest() == case['sha256'], 'Brace full input hash mismatch')
            ordered.update((case['id']+' '+h.hexdigest()+'\n').encode()); total_units += len(units); n += 1
    require(units_report['passed'] is True and units_report['cases'] == n == 720 and units_report['signed_units'] == total_units and
            units_report['catalogue_sha256'] == BALANCE_MANIFESTS['balance-simplified-full/manifest.json'] and
            units_report['ordered_case_hash_digest'] == ordered.hexdigest(), 'Incomplete or altered brace binding')
    for name in ['check_base.py','check_marked_inputs.py','check_counters.py','check_balance.py','check_release_evidence.py']:
        store.get(str(store.formal/name))
    return {'marked_cases':marked_summary, 'marked_formula_multiset_sha256':census_digest.hexdigest(),
            'base_clauses':149270,'counter_blocks':960,'counter_clauses':clause_count,
            'prefixes':7,'brace_cases':720,'brace_ordered_case_hash_digest':ordered.hexdigest(),
            'all_five_cases':3,'total_formulas':296797}


def inspect(store, build_origin, bindings):
    build, build_summary = inspect_build(store, build_origin)
    binding_summary = inspect_bindings(store, absolute_origin(str(build_origin)), build, bindings)
    return {'build':build_summary,'bindings':binding_summary,'conditional_reduction_only':True,
            'native_completion_claim':False,'unsat_refutations_checked':False}


def _prepare_stage(workspace, build_result, bindings, output):
    workspace = Path(workspace).resolve(); output = Path(output).absolute()
    absolute_origin(str(output))
    require(output.resolve() == output, 'Linked output parent forbidden')
    require(not output.exists(), 'Output must be a fresh directory')
    # Refuse the initial build before copying a large payload.
    original = read_json(build_result)
    require(original.get('passed') is True and original.get('target') == 'UniformK60.Verification' and
            REQUIRED <= set(original.get('sources', {})), 'Final complete Verification build required; no development package')
    output.mkdir(parents=True)
    store = Collector(workspace, output)
    build_origin = str(Path(build_result).resolve())
    binding_origins = {k:str(Path(v).resolve()) for k,v in bindings.items()}
    summary = inspect(store, build_origin, binding_origins)
    verifier_source = Path(__file__).resolve(); verifier_before = pin(verifier_source)
    verifier = output/'tools/formal_evidence.py'; verifier.parent.mkdir(); shutil.copyfile(verifier_source, verifier)
    require(pin(verifier) == verifier_before == pin(verifier_source), 'Verifier changed during preparation')
    store.files['tools/formal_evidence.py'] = verifier_before
    instructions = ('This is a conditional formal-reduction capsule, not native UNSAT completion.\n'
        'Verify without private paths, Lean or compiled artifacts:\n'
        '  python3 tools/formal_evidence.py verify --root . --manifest-sha256 <externally supplied hash>\n'
        'Rebuild (separate proof replay): install the pinned lean-toolchain and lake-manifest packages,\n'
        'then from workspace/k60-lean run build.py --target UniformK60.Verification --lean <lean> --packages <packages>.\n'
        'Use the four archived check_base.py/check_marked_inputs.py/check_counters.py/check_balance.py drivers\n'
        'against that new BUILD_RESULT.json. No old project .olean is included or required.\n'
        'Raw build/binding receipts retain their original paths; the manifest declares their origin mapping.\n')
    (output/'REPRODUCE.txt').write_text(instructions); store.files['REPRODUCE.txt'] = pin(output/'REPRODUCE.txt')
    store.unchanged()
    manifest = {'schema':SCHEMA,'created_utc':dt.datetime.now(dt.timezone.utc).isoformat(),'trust':TRUST,
                'origins':{'workspace':str(workspace),'compiler':original['modules'][-1]['command'][3]},
                'build_result':build_origin,'bindings':binding_origins,'files':store.files,
                'live_artifact_custody':store.custody,'live_custody_authenticated':True,'summary':summary}
    mp = output/'FORMAL_RELEASE.json'
    with mp.open('x') as stream: json.dump(manifest,stream,indent=2,sort_keys=True); stream.write('\n')
    digest = pin(mp)['sha256']; report = verify(output,digest)
    store.unchanged()
    require(pin(verifier_source) == verifier_before, 'Verifier changed during portable verification')
    return {'manifest_sha256':digest,'root':str(output),**report}


def prepare(workspace, build_result, bindings, output):
    output = Path(output).absolute(); absolute_origin(str(output))
    require(output.resolve() == output and not output.exists(), 'Output must be fresh with no linked parent')
    stage = output.with_name(output.name + '.partial-' + uuid.uuid4().hex[:12])
    try:
        result = _prepare_stage(workspace, build_result, bindings, stage)
        require(not output.exists(), 'Output appeared during preparation')
        stage.rename(output); result['root'] = str(output)
        return result
    except Exception as error:
        if stage.exists():
            manifest = stage/'FORMAL_RELEASE.json'
            if manifest.exists(): manifest.rename(stage/'REJECTED_MANIFEST.json')
            (stage/'FAILED.json').write_text(json.dumps({'passed':False,'error':str(error)},indent=2)+'\n')
        raise


def verify(root, manifest_sha256):
    store = Archive(root,manifest_sha256); manifest = store.manifest
    require(manifest.get('live_custody_authenticated') is True and manifest.get('trust') == TRUST,
            'Missing live custody gate or altered trust statement')
    require(manifest['origins']['compiler'] == store.json(manifest['build_result'])['modules'][-1]['command'][3],
            'Compiler origin mismatch')
    summary = inspect(store,manifest['build_result'],manifest['bindings'])
    require(summary == manifest['summary'], 'Recomputed formal summary disagrees')
    require(store.used | {'tools/formal_evidence.py','REPRODUCE.txt'} == set(store.files), 'Unreferenced or omitted capsule payload')
    require(store.used_custody == set(store.custody), 'Unexpected artifact custody records')
    require(pin(Path(__file__).resolve()) == store.files['tools/formal_evidence.py'], 'Verifier source differs from retained version')
    return {'passed':True,'schema':SCHEMA,'conditional_reduction_only':True,'native_completion_claim':False,
            'modules':summary['build']['modules'],'total_formulas':summary['bindings']['total_formulas']}


def self_test():
    class Tests(unittest.TestCase):
        def test_path_safety(self):
            for bad in ['/x','../x','a/../x','a//b','a/./b','a\\b','a:b','./x','a\x00b']:
                with self.assertRaises(ValueError): safe_member(bad)
            for bad in ['relative','/a/../b','/a//b','/a\\b']:
                with self.assertRaises(ValueError): absolute_origin(bad)
            s = Store('/original/work'); self.assertEqual(s.member('/original/work/x'), 'workspace/x')
            with self.assertRaises(ValueError): s.member('/original/work-else/x')
        def test_omitted_module(self):
            with self.assertRaisesRegex(ValueError,'Omitted'):
                selected_closure('UniformK60.Verification',{'UniformK60.Verification':'import UniformK60.FiniteBoundary'}, {})
            with self.assertRaisesRegex(ValueError,'unrelated'):
                selected_closure('UniformK60.Verification',{'UniformK60.Verification':'', 'UniformK60.Other':''}, {})
            with self.assertRaisesRegex(ValueError,'Unregistered'):
                selected_closure('UniformK60.Verification',{'UniformK60.Verification':'import Ramsey61.Omitted'}, {'Ramsey61.Foundations':{}})
        def test_comments_and_signatures(self):
            self.assertEqual(imports_of('/- import Bad /- nested -/ -/\nimport Good.A\n--import Bad\n'),['Good.A'])
            with self.assertRaises(ValueError): declaration('theorem t (h : False) : True := by trivial','t','(h : True) : True')
            with self.assertRaises(ValueError): audit_axioms("'t' depends on axioms: [sorryAx]")
        def test_embedded_data_custody(self):
            source='/old/formal/src/Test.lean'
            # An ordinary escaped-string decoy must not create a data dependency.
            text=r'''/- include_str "ignored" /- nested -/ -/
def dummy := "include_str \"ignored\""
'''
            text+='def cnf := include_str /- comment -/ "../data/a.cnf"\n'
            record={'path':'/old/formal/data/a.cnf','sha256':'a'*64}; data={record['path']:record}
            self.assertEqual(embedded_paths(text),['../data/a.cnf'])
            self.assertEqual(check_embedded_records(source,text,data,[record]),[record])
            for bad in [None,[],[dict(record,sha256='b'*64)],[record,record]]:
                with self.assertRaisesRegex(ValueError,'custody'):check_embedded_records(source,text,data,bad)
            with self.assertRaisesRegex(ValueError,'Unpinned'):
                embedded_records(source,'def x := include_str "../../outside"',data)
            self.assertEqual(check_embedded_records(source,'def x := 1',data,[]),[])
        def test_source_mismatch_and_symlink(self):
            with tempfile.TemporaryDirectory() as tmp:
                p=Path(tmp).resolve(); source=p/'work';source.mkdir();(source/'a').write_text('original'); out=p/'out';out.mkdir()
                s=Collector(source,out)
                with self.assertRaisesRegex(ValueError,'changed'): s.checked(source/'a',{'sha256':'0'*64})
                (source/'link').symlink_to(source/'a')
                with self.assertRaisesRegex(ValueError,'unlinked'): s.get(str(source/'link'))
                (source/'a').write_text('changed')
                with self.assertRaisesRegex(ValueError,'changed'): s.unchanged()
        def test_initial_build_rejected(self):
            with tempfile.TemporaryDirectory() as tmp:
                p=Path(tmp).resolve();b=p/'old.json';b.write_text(json.dumps({'passed':True,'target':'UniformK60.Verification','sources':{'UniformK60.Reduction':{}}}))
                with self.assertRaisesRegex(ValueError,'development'):
                    prepare(p,b,{},p/'capsule')
                self.assertFalse((p/'capsule').exists())
        def test_receipt_build_mismatch(self):
            with tempfile.TemporaryDirectory() as tmp:
                p=Path(tmp).resolve();f=p/'k60-lean/.build/final';f.mkdir(parents=True);(f/'RESULT.json').write_text(json.dumps({'passed':True,'build_result':'/wrong'}))
                out=p/'out';out.mkdir();s=Collector(p,out)
                with self.assertRaisesRegex(ValueError,'different'):
                    binding_receipt(s,f/'RESULT.json',p/'right',{'compiler_sha256':'0'*64})
        def test_base(self):
            body=generated_base();self.assertEqual(body.count(b'\n'),149270)
            self.assertEqual(sha(b'p cnf 7080 149270\n'+body),BASE_SHA)
        def test_both_binding_base_runtime_paths_retained(self):
            with tempfile.TemporaryDirectory() as tmp:
                root=Path(tmp).resolve();workspace=root/'workspace';out=root/'payload';out.mkdir()
                body=generated_base();raw=b'p cnf 7080 149270\n'+body
                for relative in ['inputs-k60-entrances/base.cnf','inputs-e-exhaustive/base.cnf']:
                    p=workspace/'k60-pilot'/relative;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(raw)
                manifest={'base':{'path':'base.cnf','sha256':BASE_SHA,'bytes':len(raw),
                          'body_sha256':sha(body),'variables':7080,'clauses':149270}}
                store=Collector(workspace,out);origins=retain_binding_bases(store,body,manifest)
                self.assertEqual(set(store.files),{
                    'workspace/k60-pilot/inputs-k60-entrances/base.cnf',
                    'workspace/k60-pilot/inputs-e-exhaustive/base.cnf'})
                for origin in origins:self.assertEqual((out/store.member(origin)).read_bytes(),raw)
                # A physically missing second copy must fail even when the first has identical bytes.
                (workspace/'k60-pilot/inputs-e-exhaustive/base.cnf').unlink()
                other=root/'other';other.mkdir()
                with self.assertRaises(ValueError):retain_binding_bases(Collector(workspace,other),body,manifest)
        def test_duplicate_json(self):
            with tempfile.TemporaryDirectory() as tmp:
                p=Path(tmp)/'x';p.write_text('{"a":1,"a":2}')
                with self.assertRaises(ValueError): read_json(p)
        def test_four_bindings_required(self):
            with self.assertRaisesRegex(ValueError,'four'):
                inspect_bindings(Store('/original/work'),'/original/build',{}, {'base':'/original/base'})
        def test_relocated_origin_mapping(self):
            with tempfile.TemporaryDirectory() as tmp:
                p=Path(tmp).resolve(); a=p/'capsule';(a/'workspace').mkdir(parents=True)
                f=a/'workspace/proof.lean';f.write_text('retained source\n')
                artifact={'path':'/nonexistent/compiler/lib/A.olean','sha256':sha(b'old artifact'),'bytes':12}
                manifest={'schema':SCHEMA,'origins':{'workspace':'/nonexistent/private/original'},
                          'files':{'workspace/proof.lean':pin(f)},
                          'live_artifact_custody':{artifact['path']:{k:v for k,v in artifact.items() if k!='path'}}}
                mp=a/'FORMAL_RELEASE.json';mp.write_text(json.dumps(manifest));digest=pin(mp)['sha256']
                b=p/'moved';a.rename(b);archive=Archive(b,digest)
                self.assertEqual(archive.get('/nonexistent/private/original/proof.lean').read_text(),'retained source\n')
                archive.artifact(artifact)
                self.assertEqual(archive.used_custody,{artifact['path']})
                with self.assertRaisesRegex(ValueError,'Conflicting'):
                    archive.artifact(dict(artifact,sha256='0'*64))
                with self.assertRaises(ValueError):archive.get('/nonexistent/private/other/proof.lean')
                (b/'extra').write_text('not in manifest')
                with self.assertRaisesRegex(ValueError,'unexpected'):Archive(b,digest)
        def test_archive_pin_and_symlink(self):
            with tempfile.TemporaryDirectory() as tmp:
                p=Path(tmp).resolve();a=p/'capsule';(a/'workspace').mkdir(parents=True)
                f=a/'workspace/a';f.write_text('one')
                manifest={'schema':SCHEMA,'origins':{'workspace':'/old'},'files':{'workspace/a':pin(f)},'live_artifact_custody':{}}
                mp=a/'FORMAL_RELEASE.json';mp.write_text(json.dumps(manifest));digest=pin(mp)['sha256']
                f.write_text('two')
                with self.assertRaisesRegex(ValueError,'Changed'):Archive(a,digest)
                f.unlink();outside=p/'outside';outside.write_text('one');f.symlink_to(outside)
                with self.assertRaisesRegex(ValueError,'symlink'):Archive(a,digest)
    result=unittest.TextTestRunner(verbosity=2).run(unittest.defaultTestLoader.loadTestsFromTestCase(Tests))
    require(result.wasSuccessful(),'Formal portability self-tests failed')


def main():
    parser=argparse.ArgumentParser(description=__doc__);commands=parser.add_subparsers(dest='command',required=True)
    p=commands.add_parser('prepare');p.add_argument('--workspace',type=Path,required=True);p.add_argument('--build-result',type=Path,required=True)
    for name in ['base','marked','counter','balance']:p.add_argument('--'+name+'-binding',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True)
    v=commands.add_parser('verify');v.add_argument('--root',type=Path,required=True);v.add_argument('--manifest-sha256',required=True)
    commands.add_parser('self-test');args=parser.parse_args()
    if args.command=='self-test':self_test();return
    if args.command=='verify':report=verify(args.root,args.manifest_sha256)
    else:report=prepare(args.workspace,args.build_result,{n:getattr(args,n+'_binding') for n in ['base','marked','counter','balance']},args.output)
    print(json.dumps(report,indent=2,sort_keys=True))


if __name__=='__main__': main()
