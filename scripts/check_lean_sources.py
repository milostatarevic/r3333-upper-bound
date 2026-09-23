#!/usr/bin/env python3
"""Source/manifest controls for the complete package; no Lean or solver runs.

This engineering audit supplements Lean checking. Executable reproduction
sources under formal/reproduce are separate from the manifest-listed proofs.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import runpy
import sys

ROOT = Path(__file__).resolve().parents[1]
FORMAL = ROOT / 'formal'
ACCEPTED_MANIFEST_PIN = ROOT / 'publication/checks/ACCEPTED_MATH_MANIFEST.sha256'
BUILD_IDENTITY_SHA = '5c92104305178b44756f24ab49aaca626106c4bdbc57c0203910c12d07acfd8d'
IDENTITY_MODULES = {'Ramsey61.Conditional': 5, 'Ramsey61.Selector': 1,
                    'R4333Lean.Attaching61Reduction': 3, 'R4333Lean.CriticalCatalogues': 1}
MODULE_COUNT, DATA_COUNT = 1809, 110
ROOTS = ('PricingIntegration.NativeWholeProof', 'CompletionC.CommonCaseCount',
         'PricingIntegration.NativeWholeCount', 'PricingABD.CommonSuffixCache',
         'PricingG.UUQEmissionIdentity')
CONTROL_FILES = {'lean-toolchain', 'lakefile.toml', 'lake-manifest.json', 'build.py', 'BUILD.md'}
HELPER = 'src/R4333Lean/CheckedLRAT.lean'
HELPER_SHA = '0dc50a516ce88c897aa9c1b71baedb1f693b010cdd644886f83dd09fd677edc5'
HELPER_LINES = {
    40: 'let cnfText ← unsafe evalTerm String (mkConst ``String) cnf',
    41: 'let lratText ← unsafe evalTerm String (mkConst ``String) lrat',
}
FORBIDDEN = {
    'proof escape/declaration': re.compile(r'\b(?:sorry|sorryAx|admit|native_decide|axiom|unsafe|partial|implemented_by|extern)\b'),
    'native reduction escape': re.compile(r'\b(?:Lean\.)?(?:ofReduceBool|ofReduceNat|trustCompiler)\b'),
    'kernel bypass': re.compile(r'\bdebug\.skipKernelTC\b'),
    'unreviewed elaborator execution': re.compile(r'#eval\b|\brun_elab\b'),
}
DIGEST = re.compile(r'[0-9a-f]{64}\Z')


def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def require_accepted_manifest(current_sha256, accepted_sha256):
    """Bind this package to the manifest named by final accepted build evidence.

    The integration caller must obtain accepted_sha256 from the owner's final
    accepted record. This helper deliberately defines no replacement receipt.
    """
    require(isinstance(accepted_sha256, str) and DIGEST.fullmatch(accepted_sha256),
            'Missing/invalid accepted full-build manifest hash')
    require(current_sha256 == accepted_sha256,
            'Current source manifest is not the accepted full-build manifest')


def read_accepted_manifest_pin(path=ACCEPTED_MANIFEST_PIN):
    path = Path(path)
    require(path.is_file() and not path.is_symlink(), 'Missing/symlink accepted manifest pin: ' + str(path))
    raw = path.read_bytes()
    require(re.fullmatch(rb'[0-9a-f]{64}\n', raw) is not None,
            'Accepted manifest pin must be exactly 64 lowercase hex characters and LF')
    return raw[:-1].decode('ascii')


def require_accepted_package(formal, current_sha256, accepted_sha256):
    """Bind current proof sources to the recorded build without source snapshots.

    Reverse the exact documentation substitutions and recover the original
    source hashes and full manifest digest. Declarations/proofs cannot change.
    """
    require(isinstance(accepted_sha256, str) and DIGEST.fullmatch(accepted_sha256),
            'Missing/invalid accepted full-build manifest hash')
    if current_sha256 == accepted_sha256:
        return {'kind': 'exact_accepted_build', 'baseline_manifest_sha256': accepted_sha256}
    formal = Path(formal)
    identity = strict_json(pinned(formal, {'path': 'BUILD_IDENTITY.json', 'sha256': BUILD_IDENTITY_SHA}))
    require_accepted_manifest(identity['baseline_manifest_sha256'], accepted_sha256)
    raw = (formal / 'SOURCE_MANIFEST.json').read_bytes()
    require(sha(raw) == current_sha256, 'Current manifest hash differs')
    manifest = strict_json(raw)
    rows = identity['modules']
    require(len(rows) == len(IDENTITY_MODULES) and
            {r['module'] for r in rows} == set(IDENTITY_MODULES), 'Build-identity module census differs')
    for revision in rows:
        name = revision['module']; row = manifest['modules'][name]
        require(row['path'] == 'src/' + name.replace('.', '/') + '.lean', 'Build-identity source path differs')
        text = pinned(formal, row).decode('utf-8')
        require(len(revision['comments']) == IDENTITY_MODULES[name], 'Documentation-span census differs')
        for comment in reversed(revision['comments']):
            old, new = comment['before'], comment['after']
            for block in (old, new):
                require(block.startswith(('/--', '/-!')) and block.endswith('-/') and
                        '/-' not in block[3:-2] and '-/' not in block[3:-2],
                        'Substitution must be one closed documentation comment')
            require(text.count(new) == 1, 'Documentation span is not unique')
            text = text.replace(new, old, 1)
        original = text.encode('utf-8')
        require(sha(original) == revision['original_source_sha256'], 'Proof source differs from recorded build')
        row.update(sha256=sha(original), bytes=len(original))
    original_manifest = (json.dumps(manifest, indent=2) + '\n').encode('utf-8')
    require_accepted_manifest(sha(original_manifest), accepted_sha256)
    return {'kind': 'recorded_build_sources_with_identical_declarations',
            'baseline_manifest_sha256': accepted_sha256,
            'current_manifest_sha256': current_sha256,
            'build_identity_sha256': BUILD_IDENTITY_SHA,
            'complete_theorem_rebuilt': False}


def mask_noncode(text):
    result = list(text)
    i = 0
    def blank(k):
        if result[k] != '\n':
            result[k] = ' '
    while i < len(text):
        if text.startswith('--', i):
            while i < len(text) and text[i] != '\n':
                blank(i); i += 1
        elif text.startswith('/-', i):
            depth = 1
            blank(i); blank(i + 1); i += 2
            while i < len(text) and depth:
                if text.startswith('/-', i):
                    depth += 1; blank(i); blank(i + 1); i += 2
                elif text.startswith('-/', i):
                    depth -= 1; blank(i); blank(i + 1); i += 2
                else:
                    blank(i); i += 1
            require(depth == 0, 'Unterminated block comment')
        elif text[i] == '«':
            # Quoted identifiers can name escape constants; keep their contents
            # visible to the conservative token scan instead of hiding them.
            end = text.find('»', i + 1)
            require(end >= 0, 'Unterminated quoted identifier')
            i = end + 1
        elif text[i] == '"':
            blank(i); i += 1
            closed = False
            while i < len(text):
                char = text[i]; blank(i); i += 1
                if char == '\\' and i < len(text):
                    blank(i); i += 1
                elif char == '"':
                    closed = True; break
            require(closed, 'Unterminated string')
        else:
            i += 1
    return ''.join(result)


def violations(text):
    code = mask_noncode(text)
    return [(label, code.count('\n', 0, match.start()) + 1)
            for label, pattern in FORBIDDEN.items() for match in pattern.finditer(code)]


def proof_violations(relative, payload):
    text = payload.decode('utf-8')
    found = violations(text)
    if relative == HELPER:
        require(sha(payload) == HELPER_SHA, 'Reviewed LRAT helper hash changed')
        require(found == [('proof escape/declaration', 40), ('proof escape/declaration', 41)],
                'Reviewed LRAT helper exception changed')
        lines = text.splitlines()
        require(all(lines[line - 1].strip() == expected for line, expected in HELPER_LINES.items()),
                'Reviewed LRAT helper statements changed')
        return []
    return found


def strict_json(payload):
    def unique(pairs):
        result = {}
        for key, value in pairs:
            require(key not in result, 'Duplicate JSON key: ' + key)
            result[key] = value
        return result
    return json.loads(payload, object_pairs_hook=unique)


def pinned(root, row):
    relative = row['path']
    require(isinstance(relative, str) and not Path(relative).is_absolute() and
            '..' not in Path(relative).parts, 'Invalid pinned path')
    path = root / relative
    require(path.is_file() and not path.is_symlink(), 'Missing/symlink pinned file: ' + relative)
    payload = path.read_bytes()
    require(DIGEST.fullmatch(row.get('sha256', '')) and sha(payload) == row['sha256'],
            'Source hash mismatch: ' + relative)
    if 'bytes' in row:
        require(row['bytes'] == len(payload), 'Source size mismatch: ' + relative)
    return payload


def inspect_package(root, *, module_count=MODULE_COUNT, data_count=DATA_COUNT, roots=ROOTS):
    root = root.resolve(strict=True)
    require(not (root / 'SOURCE_MANIFEST.json').is_symlink(), 'Symlink source manifest')
    raw = (root / 'SOURCE_MANIFEST.json').read_bytes()
    manifest = strict_json(raw)
    modules, data, files = manifest['modules'], manifest['data'], manifest['files']
    require(isinstance(modules, dict) and len(modules) == module_count, 'Proof module census changed')
    require(isinstance(data, list) and len(data) == data_count, 'Embedded data census changed')
    require(tuple(manifest['roots']) == tuple(roots), 'Default theorem roots changed')
    require(isinstance(files, list) and len(files) == len(CONTROL_FILES) and
            {r['path'] for r in files} == CONTROL_FILES, 'Build-control census changed')
    expected_sources = {row['path'] for row in modules.values()}
    expected_data = {row['path'] for row in data}
    require(len(expected_sources) == module_count and len(expected_data) == data_count,
            'Duplicate source or embedded-data paths')
    require(not expected_sources & expected_data, 'Proof source also listed as embedded data')
    actual = set()
    outside_proof = []
    for directory, subdirs, names in os.walk(root, followlinks=False):
        if Path(directory) == root:
            subdirs[:] = [name for name in subdirs if name not in ('.lake', '.build')]
        for name in [*subdirs, *names]:
            path = Path(directory) / name
            rel = path.relative_to(root)
            require(not path.is_symlink(), 'Package symlink: ' + str(rel))
            if path.is_file() and rel.parts[0] == 'src':
                actual.add(rel.as_posix())
            elif path.is_file() and path.suffix == '.lean':
                require(rel.parts[0] == 'reproduce', 'Unexpected Lean source outside src/reproduce: ' + str(rel))
                outside_proof.append(rel.as_posix())
    require(actual == expected_sources | expected_data, 'Exact src source/data filesystem census changed')
    for row in [*modules.values(), *data, *files]:
        pinned(root, row)
    failures = []
    for row in modules.values():
        for label, line in proof_violations(row['path'], (root / row['path']).read_bytes()):
            failures.append(f"{row['path']}:{line}: {label}")
    require(not failures, '\n'.join(failures))

    # Run only the package's pinned pure static validator, never its main/build.
    builder = runpy.run_path(str(root / 'build.py'), run_name='ci_package_static_validation')
    checked, selected, checked_data, replay = builder['static_check'](root, manifest, [], False)
    require(set(checked) == selected == set(modules), 'Manifest is not exactly the default-root closure')
    require(set(checked_data) == expected_data, 'Static validator data census differs')
    external = {dep for row in modules.values() for dep in row['imports'] if dep not in modules}
    require(set(manifest['external_imports']) == external and
            len(manifest['external_imports']) == len(external), 'External-import census changed')
    require(all(dep.split('.')[0] in {'Mathlib', 'Std', 'Lean', 'Init', 'Batteries',
                                     'Aesop', 'Qq', 'Plausible', 'ImportGraph',
                                     'ProofWidgets', 'LeanSearchClient'} for dep in external),
            'Unresolved project import treated as external')
    order = manifest['topological_order']
    require(len(order) == len(modules) and set(order) == set(modules), 'Topological module census changed')
    positions = {name: i for i, name in enumerate(order)}
    require(all(positions[d] < positions[m] for m, row in modules.items()
                for d in row['imports'] if d in modules), 'Invalid topological order')
    duplicate = root / 'reproduce/common/lean/PricingABD/CommonSuffixCache.lean'
    if duplicate.exists():
        require(duplicate.read_bytes() == (root / 'src/PricingABD/CommonSuffixCache.lean').read_bytes(),
                'Supplemental reproduction copy differs from proof source')
    classification = root.parent / 'classification'
    if (classification / 'MANIFEST.json').is_file():
        catalogue = strict_json((classification / 'MANIFEST.json').read_bytes())
        for row in catalogue['files']:
            payload = pinned(classification, row)
            if row['kind'] in ('lean_source', 'cnf', 'lrat'):
                require((root / 'src' / row['path']).read_bytes() == payload,
                        'Classification source/data mirror differs: ' + row['path'])
    return {'status': 'PASS_PACKAGE_SOURCE_AND_MANIFEST_CONTROLS',
            'manifest_sha256': sha(raw), 'proof_modules': len(modules), 'embedded_data_files': len(data),
            'default_roots': list(roots), 'exact_default_root_closure': True,
            'reviewed_helper': {'path': HELPER, 'sha256': HELPER_SHA, 'unsafe_occurrences': 2},
            'reproduction_lean_sources_not_proof_scanned': sorted(outside_proof),
            'certificate_command_modules_not_executed': replay,
            'new_compiler_calls': 0, 'new_solver_calls': 0, 'new_certificate_replays': 0,
            'scope': 'Engineering source/hash/import/census controls and pinned builder static validation; '
                     'no theorem compilation, native input binding, or UNSAT verification.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--formal', type=Path, default=FORMAL)
    parser.add_argument('--report', type=Path)
    args = parser.parse_args()
    accepted = read_accepted_manifest_pin()
    report = inspect_package(args.formal)
    report['build_acceptance'] = require_accepted_package(args.formal, report['manifest_sha256'], accepted)
    report['accepted_manifest_pin'] = str(ACCEPTED_MANIFEST_PIN.relative_to(ROOT))
    if args.report:
        args.report.parent.mkdir(parents=True, exist_ok=True)
        with args.report.open('x') as stream:
            json.dump(report, stream, indent=2, sort_keys=True); stream.write('\n')
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == '__main__':
    try:
        main()
    except (ValueError, OSError, KeyError, TypeError, RuntimeError) as error:
        print('FAIL: ' + str(error), file=sys.stderr)
        raise SystemExit(1)
