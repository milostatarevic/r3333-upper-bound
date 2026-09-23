#!/usr/bin/env python3
"""Build and audit a five-module encoding target, never the complete theorem."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

from check_lean_sources import (FORMAL, inspect_package, require, strict_json,
                                read_accepted_manifest_pin, require_accepted_package)

TARGET = 'PricingIntegration.NativeColoringClauses'
MODULES = {TARGET, 'PricingIntegration.NativePrimaryCore', 'Ramsey61.CEncodingCore',
           'Ramsey61.DenseCounter', 'Ramsey61.Foundations'}
THEOREMS = {TARGET + '.physicalValuation_physical', TARGET + '.physicalValuation_triangles'}
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
DEPENDENCY = re.compile(r"'([A-Za-z0-9_.]+)' depends on axioms:\s*\[([^\]]*)\]")
AXIOM_FREE = re.compile(r"'([A-Za-z0-9_.]+)' does not depend on any axioms")


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def validate_report(text):
    reports = {}
    for name, raw in DEPENDENCY.findall(text):
        require(name not in reports, 'Duplicate axiom report: ' + name)
        reports[name] = {x.strip() for x in raw.split(',') if x.strip()}
    for name in AXIOM_FREE.findall(text):
        require(name not in reports, 'Duplicate axiom report: ' + name)
        reports[name] = set()
    require(set(reports) == THEOREMS, 'Missing or unexpected encoding-theorem axiom report')
    for name, used in reports.items():
        require(used <= ALLOWED, name + ' uses unapproved axioms: ' + str(sorted(used - ALLOWED)))
    return {name: sorted(used) for name, used in sorted(reports.items())}


def check_small_closure(manifest):
    modules = manifest['modules']
    require(TARGET in modules, 'Small target missing from manifest')
    selected = set()
    def visit(module):
        if module in selected or module not in modules:
            return
        selected.add(module)
        for dependency in modules[module]['imports']:
            visit(dependency)
    visit(TARGET)
    require(selected == MODULES, 'Small-target preflight closure is not exactly five approved modules')


def audit_run(formal, run, manifest_sha):
    result = strict_json((run / 'BUILD_RESULT.json').read_bytes())
    require(result.get('status') == 'PASS', 'Small-target build did not pass')
    require(result.get('targets') == [TARGET] and result.get('selected_modules') == 5 and
            set(result.get('completed', [])) == MODULES and len(result['completed']) == 5,
            'Unexpected small-target build closure')
    require(result.get('jobs') == 1 and result.get('certificate_command_modules') == [] and
            result.get('new_solver_calls') == 0 and result.get('baseline_project_artifacts_reused') is False,
            'Small-target execution scope changed')
    require(result.get('manifest_sha256') == manifest_sha == sha(formal / 'SOURCE_MANIFEST.json'),
            'Build manifest identity changed')
    manifest = strict_json((formal / 'SOURCE_MANIFEST.json').read_bytes())
    for module in sorted(MODULES):
        folder = run / 'modules' / module
        receipt = strict_json((folder / 'receipt.json').read_bytes())
        require(receipt.get('module') == module and receipt.get('status') == 'PASS' and
                receipt.get('exit_code') == 0, 'Missing/failed module receipt: ' + module)
        require(receipt.get('source') == manifest['modules'][module], 'Module source receipt differs: ' + module)
        require(receipt.get('log_sha256') == sha(folder / 'lean.log'), 'Module log identity differs: ' + module)
    reports = validate_report((run / 'modules' / TARGET / 'lean.log').read_text())
    return {'status': 'PASS_SMALL_LEAN_ENCODING_BUILD_AND_AXIOM_AUDIT',
            'manifest_sha256': manifest_sha, 'target': TARGET, 'modules': sorted(MODULES),
            'theorem_axioms': reports, 'build_run': str(run),
            'complete_theorem_rebuilt': False, 'classification_certificates_replayed': False,
            'native_input_bindings_checked': False, 'native_unsat_verified': False,
            'scope': 'Fresh five-module coloring-encoding build and its two theorem axiom reports only.'}


def copy_receipts(run, artifacts):
    # Deliberately omit lib/, output.olean and all compiled companions.
    destination = artifacts / 'small-lean-build'
    destination.mkdir()
    if (run / 'BUILD_RESULT.json').is_file():
        shutil.copyfile(run / 'BUILD_RESULT.json', destination / 'BUILD_RESULT.json')
    for folder in sorted((run / 'modules').glob('*')):
        if not folder.is_dir():
            continue
        target = destination / 'modules' / folder.name
        target.mkdir(parents=True)
        for name in ('receipt.json', 'lean.log'):
            if (folder / name).is_file():
                shutil.copyfile(folder / name, target / name)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--formal', type=Path, default=FORMAL)
    parser.add_argument('--artifacts', type=Path, default=Path('verification-artifacts'))
    parser.add_argument('--audit-output', type=Path, help='Audit an existing target log only; no compilation')
    args = parser.parse_args()
    formal = args.formal.resolve(strict=True)
    accepted = read_accepted_manifest_pin()
    static = inspect_package(formal)
    require_accepted_package(formal, static['manifest_sha256'], accepted)
    check_small_closure(strict_json((formal / 'SOURCE_MANIFEST.json').read_bytes()))
    if args.audit_output:
        print(json.dumps({'status': 'PASS_EXISTING_SMALL_TARGET_AXIOM_LOG_ONLY',
                          'theorem_axioms': validate_report(args.audit_output.read_text()),
                          'fresh_compilation': False}, indent=2))
        return
    lake = os.environ.get('LAKE') or shutil.which('lake')
    require(lake is not None, 'lake is unavailable; install the pinned toolchain/cache')
    artifacts = args.artifacts.resolve()
    artifacts.mkdir(parents=True, exist_ok=True)
    runs = formal / '.build/runs'
    before = set(runs.iterdir()) if runs.exists() else set()
    env = dict(os.environ, LEAN_NUM_THREADS='1', PYTHONDONTWRITEBYTECODE='1')
    command = [lake, 'env', sys.executable, '-B', 'build.py', '--target', TARGET,
               '--no-certificate-replay', '--jobs', '1']
    print('Building five-module target: ' + TARGET, flush=True)
    code = subprocess.run(command, cwd=formal, env=env, check=False).returncode
    after = set(runs.iterdir()) if runs.exists() else set()
    created = after - before
    require(len(created) == 1, 'Expected exactly one new isolated build run')
    run = created.pop()
    copy_receipts(run, artifacts)
    require(code == 0, 'Small-target builder failed; retained its logs and receipts')
    result = audit_run(formal, run, static['manifest_sha256'])
    with (artifacts / 'small-lean-audit.json').open('x') as stream:
        json.dump(result, stream, indent=2, sort_keys=True); stream.write('\n')
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == '__main__':
    try:
        main()
    except (ValueError, OSError, KeyError, TypeError, RuntimeError, subprocess.SubprocessError) as error:
        print('FAIL: ' + str(error), file=sys.stderr)
        raise SystemExit(1)
