#!/usr/bin/env python3
"""Build/audit the small encoding target, or explicitly request the full reduction."""
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

TARGET = 'UniformK60.CoreCounts'
MODULES = {TARGET, 'UniformK60.Core', 'UniformK60.Physical',
           'UniformK61.CNF', 'Ramsey61.Foundations'}
THEOREMS = {'UniformK60.Core.baseCNF_length', 'UniformK60.Core.coloring_satisfies_formula'}
FULL_TARGET = 'UniformK60.Verification'
FULL_THEOREMS = {
    'UniformK60.ramsey60_of_exact_unsat',
    'UniformK60.CEntranceComplete.no_entrance_of_all_unsat',
    'UniformK60.ramsey60_of_reduction_obligations',
    *THEOREMS,
}
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
DEPENDENCY = re.compile(r"'([A-Za-z0-9_.]+)' depends on axioms:\s*\[([^\]]*)\]")
AXIOM_FREE = re.compile(r"'([A-Za-z0-9_.]+)' does not depend on any axioms")


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def validate_report(text, theorems=THEOREMS):
    reports = {}
    for name, raw in DEPENDENCY.findall(text):
        require(name not in reports, 'Duplicate axiom report: ' + name)
        reports[name] = {x.strip() for x in raw.split(',') if x.strip()}
    for name in AXIOM_FREE.findall(text):
        require(name not in reports, 'Duplicate axiom report: ' + name)
        reports[name] = set()
    require(set(reports) == theorems, 'Missing or unexpected theorem axiom report')
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


def audit_run(formal, run, manifest_sha, *, full=False):
    manifest = strict_json((formal / 'SOURCE_MANIFEST.json').read_bytes())
    target = FULL_TARGET if full else TARGET
    modules = set(manifest['modules']) if full else MODULES
    result = strict_json((run / 'BUILD_RESULT.json').read_bytes())
    require(result.get('status') == 'PASS', 'Target build did not pass')
    require(result.get('targets') == [target] and result.get('selected_modules') == len(modules) and
            set(result.get('completed', [])) == modules and len(result['completed']) == len(modules),
            'Unexpected target build closure')
    certs = result.get('certificate_command_modules')
    require(isinstance(certs, list) and len(certs) == len(set(certs)) and set(certs) <= modules,
            'Invalid certificate-command census')
    if full:
        # Source inspection calls only the pinned builder's pure static validator.
        static = inspect_package(formal)
        require(certs == static['certificate_command_modules_not_executed'],
                'Full-build certificate-command census differs')
    else:
        require(certs == [], 'Small build replayed certificates')
    require(result.get('jobs') == 1 and result.get('new_solver_calls') == 0 and
            result.get('baseline_project_artifacts_reused') is False, 'Target execution scope changed')
    require(result.get('manifest_sha256') == manifest_sha == sha(formal / 'SOURCE_MANIFEST.json'),
            'Build manifest identity changed')
    for module in sorted(modules):
        folder = run / 'modules' / module
        receipt = strict_json((folder / 'receipt.json').read_bytes())
        require(receipt.get('module') == module and receipt.get('status') == 'PASS' and
                receipt.get('exit_code') == 0, 'Missing/failed module receipt: ' + module)
        require(receipt.get('source') == manifest['modules'][module], 'Module source receipt differs: ' + module)
        require(receipt.get('log_sha256') == sha(folder / 'lean.log'), 'Module log identity differs: ' + module)
    reports = validate_report((run / 'modules' / target / 'lean.log').read_text(),
                              FULL_THEOREMS if full else THEOREMS)
    return {'status': ('PASS_FULL_LEAN_REDUCTION_BUILD_AND_AXIOM_AUDIT' if full else
                       'PASS_SMALL_LEAN_ENCODING_BUILD_AND_AXIOM_AUDIT'),
            'manifest_sha256': manifest_sha, 'target': target, 'modules': sorted(modules),
            'theorem_axioms': reports, 'build_run': str(run),
            'complete_theorem_rebuilt': full, 'classification_certificates_replayed': bool(certs),
            'native_input_bindings_checked': False, 'native_unsat_verified': False,
            'scope': ('Fresh full conditional reduction build and its five theorem axiom reports; '
                      'native UNSAT remains an external premise.' if full else
                      'Fresh five-module coloring-encoding build and its two theorem axiom reports only.')}


def copy_receipts(run, artifacts, label='small-lean-build'):
    # Deliberately omit lib/, output.olean and all compiled companions.
    destination = artifacts / label
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
    parser.add_argument('--full', action='store_true', help='Build all selected sources and replay classification certificates')
    parser.add_argument('--artifacts', type=Path, default=Path('verification-artifacts'))
    parser.add_argument('--audit-output', type=Path, help='Audit an existing target log only; no compilation')
    args = parser.parse_args()
    formal = args.formal.resolve(strict=True)
    accepted = read_accepted_manifest_pin()
    static = inspect_package(formal)
    require_accepted_package(formal, static['manifest_sha256'], accepted)
    if not args.full:
        check_small_closure(strict_json((formal / 'SOURCE_MANIFEST.json').read_bytes()))
    target = FULL_TARGET if args.full else TARGET
    label = 'full-lean' if args.full else 'small-lean'
    if args.audit_output:
        print(json.dumps({'status': 'PASS_EXISTING_TARGET_AXIOM_LOG_ONLY',
                          'theorem_axioms': validate_report(args.audit_output.read_text(), FULL_THEOREMS if args.full else THEOREMS),
                          'fresh_compilation': False}, indent=2))
        return
    lake = os.environ.get('LAKE') or shutil.which('lake')
    require(lake is not None, 'lake is unavailable; install the pinned toolchain/cache')
    artifacts = args.artifacts.resolve()
    artifacts.mkdir(parents=True, exist_ok=True)
    runs = formal / '.build/runs'
    before = set(runs.iterdir()) if runs.exists() else set()
    env = dict(os.environ, LEAN_NUM_THREADS='1', PYTHONDONTWRITEBYTECODE='1')
    command = [lake, 'env', sys.executable, '-B', 'build.py', '--target', target, '--jobs', '1']
    if not args.full:
        command.append('--no-certificate-replay')
    print('Building target: ' + target, flush=True)
    code = subprocess.run(command, cwd=formal, env=env, check=False).returncode
    after = set(runs.iterdir()) if runs.exists() else set()
    created = after - before
    require(len(created) == 1, 'Expected exactly one new isolated build run')
    run = created.pop()
    copy_receipts(run, artifacts, label + '-build')
    require(code == 0, 'Target builder failed; retained its logs and receipts')
    result = audit_run(formal, run, static['manifest_sha256'], full=args.full)
    with (artifacts / (label + '-audit.json')).open('x') as stream:
        json.dump(result, stream, indent=2, sort_keys=True); stream.write('\n')
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == '__main__':
    try:
        main()
    except (ValueError, OSError, KeyError, TypeError, RuntimeError, subprocess.SubprocessError) as error:
        print('FAIL: ' + str(error), file=sys.stderr)
        raise SystemExit(1)
