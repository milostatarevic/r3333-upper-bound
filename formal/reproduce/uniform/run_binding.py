#!/usr/bin/env python3
"""Execute and check the complete uniform input binding from a fresh Lean build.

Run through `lake env python3` from formal/. No SAT solver or proof build is
launched. A complete successful current-source build is required.
"""
import argparse
import importlib.util
import json
import os
import re
from pathlib import Path
import subprocess
import sys
import time
from datetime import datetime, timezone

sys.dont_write_bytecode = True


def need(ok, message):
    if not ok:
        raise ValueError(message)


def pin(path):
    import hashlib
    path = Path(path)
    h, size = hashlib.sha256(), 0
    with path.open('rb') as stream:
        for data in iter(lambda: stream.read(1 << 20), b''):
            h.update(data); size += len(data)
    return {'path':str(path), 'sha256':h.hexdigest(), 'bytes':size}


def write_once(path, value):
    with path.open('x') as stream:
        json.dump(value, stream, indent=2); stream.write('\n')


def inspect_build(root, directory):
    result_path, manifest_path = directory/'BUILD_RESULT.json', root/'SOURCE_MANIFEST.json'
    result = json.loads(result_path.read_text())
    manifest = json.loads(manifest_path.read_text())
    need(result.get('status') == 'PASS' and result.get('baseline_project_artifacts_reused') is False,
         'A completed source-only build is required; partial/static builds are insufficient')
    need(not result.get('failures') and not result.get('pending') and not result.get('interrupted'),
         'Build has unfinished or failed work')
    need(result.get('manifest_sha256') == pin(manifest_path)['sha256'], 'Build/source manifest mismatch')
    controls = manifest['files']
    if isinstance(controls, dict):
        controls = [dict(v, path=k) if isinstance(v, dict) else {'path':k, 'sha256':v}
                    for k,v in controls.items()]
    builder = next(r for r in controls if r['path'] == 'build.py')
    need(pin(root/'build.py')['sha256'] == builder['sha256'], 'Builder source pin mismatch')
    spec = importlib.util.spec_from_file_location('_uniform_source_build', root/'build.py')
    build = importlib.util.module_from_spec(spec); spec.loader.exec_module(build)
    modules, selected, data, _ = build.static_check(root, manifest, result['targets'], False)
    need('UniformK61.WholeProof' in selected, 'Build does not contain the uniform whole-proof endpoint')
    need(set(result['completed']) == selected and len(result['completed']) == len(selected),
         'Build result does not cover its exact source closure')
    binary, compiler, paths = build.runtime(root, manifest)
    need(compiler == result['compiler'], 'Compiler or locked dependency runtime differs from the build')
    output = directory/'lib'
    expected_outputs = {output/Path(*m.split('.')).with_suffix('.olean') for m in selected}
    need(set(output.rglob('*.olean')) == expected_outputs, 'Build library has missing or extraneous project modules')
    runtime_pins, receipts, logs, artifacts = {}, [], [], {}
    def artifact_group(path):
        key = str(path)
        if key not in artifacts:
            artifacts[key] = build.artifact_pins(path)
            need(artifacts[key] and artifacts[key][0]['path'] == key, 'Missing runtime artifact')
        return artifacts[key]
    for module in sorted(selected):
        receipt_path = directory/'modules'/module/'receipt.json'
        receipt = json.loads(receipt_path.read_text())
        row = modules[module]
        log = pin(directory/'modules'/module/'lean.log')
        need(log['sha256'] == receipt.get('log_sha256'), 'Compiler log changed: '+module)
        logs.append(log)
        need(receipt.get('status') == 'PASS' and receipt.get('exit_code') == 0
             and receipt['module'] == module and receipt['source'] == row,
             'Invalid module receipt: '+module)
        need(receipt['compiler_sha256'] == compiler['sha256'], 'Module compiler mismatch: '+module)
        source = root/row['path']
        attempt = directory/'modules'/module/'output.olean'
        command = [str(binary), '-j1', '-o', str(attempt), str(source)]
        need(receipt['command'] == command, 'Unexpected build command: '+module)
        need(receipt['LEAN_PATH'] == os.pathsep.join(map(str, [output]+paths)),
             'Module used a different library path: '+module)
        accepted = output/Path(*module.split('.')).with_suffix('.olean')
        apins, tpins = artifact_group(accepted), artifact_group(attempt)
        need(apins[0]['sha256'] == receipt['artifact_sha256'], 'Accepted module hash mismatch: '+module)
        need([(p['sha256'],p['bytes']) for p in apins] == [(p['sha256'],p['bytes']) for p in tpins],
             'Accepted runtime companions differ from the compiler output: '+module)
        direct = []
        for imported in row['imports']:
            relative = Path(*imported.split('.')).with_suffix('.olean')
            search = [output] if imported in modules else paths
            found = next((p/relative for p in search if (p/relative).is_file()), None)
            need(found is not None, 'Missing imported artifact: '+imported)
            direct.extend(artifact_group(found))
        need(receipt['import_artifacts'] == direct, 'Imported runtime artifact mismatch: '+module)
        for record in apins+tpins+direct:
            runtime_pins[record['path']] = record
        receipts.append(pin(receipt_path))
    return build, modules, selected, binary, compiler, paths, {
        'build_result':pin(result_path), 'source_manifest':pin(manifest_path),
        'module_receipts':receipts, 'module_logs':logs, 'runtime_artifacts':list(runtime_pins.values()),
        'compiler':compiler, 'selected_modules':len(selected)}


def run(command, cwd, env, log_path):
    started = time.monotonic()
    with log_path.open('xb') as log:
        child = subprocess.Popen(command, cwd=cwd, env=env, stdout=log, stderr=subprocess.STDOUT)
        if hasattr(os, 'wait4'):
            _, status, usage = os.wait4(child.pid, 0)
            child.returncode = os.waitstatus_to_exitcode(status)
            cpu, rss = usage.ru_utime+usage.ru_stime, usage.ru_maxrss*(1 if sys.platform == 'darwin' else 1024)
        else:
            child.wait(); cpu, rss = None, None
    return {'command':command, 'exit_code':child.returncode, 'CPU_seconds':cpu,
            'peak_RSS_bytes':rss, 'elapsed_seconds':time.monotonic()-started, 'log':pin(log_path)}


def check_axiom_reports(text):
    expected = {'UniformK61.WholeProof.ramsey61',
                'UniformK61.WholeProof.native_case_count'}
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    pattern = re.compile(
        r"'([^'\n]+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)")
    matches = list(pattern.finditer(text))
    need(len(matches) == 2, 'Expected exactly two final-theorem axiom reports')
    reports, position = {}, 0
    for match in matches:
        need(not text[position:match.start()].strip(), 'Unexpected text in final-theorem audit')
        name = match.group(1)
        need(name in expected and name not in reports, 'Unexpected or repeated axiom-report declaration')
        axioms = [] if not match.group(2) else [a.strip() for a in match.group(2).split(',')]
        need(len(axioms) == len(set(axioms)) and set(axioms) <= allowed,
             'Nonstandard or malformed axiom dependency: '+name)
        reports[name] = axioms
        position = match.end()
    need(not text[position:].strip() and set(reports) == expected, 'Incomplete or extra axiom audit output')
    return reports


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--build-dir', type=Path, required=True)
    parser.add_argument('--inputs', type=Path, required=True)
    parser.add_argument('--output-dir', type=Path, required=True)
    parser.add_argument('--case-table', type=Path,
                        help='The current reproduce/data/marked_uu.json finite identity table')
    args = parser.parse_args()
    directory, inputs, destination = (p.resolve() for p in (args.build_dir,args.inputs,args.output_dir))
    need(not destination.exists(), 'Output directory must be fresh')
    destination.mkdir(parents=True)
    here = Path(__file__).resolve().parent
    root = here.parents[1]
    case_table = (args.case_table or root.parent/'reproduce/data/marked_uu.json').resolve()
    result = {'schema':'UNIFORM_K61_FRESH_BUILD_BINDING_1', 'status':'FAIL',
              'started_utc':datetime.now(timezone.utc).isoformat(), 'new_solver_calls':0, 'executions':[]}
    try:
        build, modules, selected, binary, compiler, paths, custody = inspect_build(root, directory)
        result['build_custody'] = custody
        input_pins = [pin(inputs/name) for name in ('MANIFEST.json','cases.jsonl.gz','base.clauses')]
        input_pins += [pin(inputs/'balanced'/(owner+'.cnf')) for owner in ('UU','UT','TT')]
        result['native_inputs'] = input_pins
        tools = [here/name for name in ('run_binding.py','check_all.py','check_common.py',
                 'check_c_entrance.py','check_balance.py','check_marked_uu.py','EmitCommon.lean',
                 'EmitCEntrance.lean','EmitBalanced.lean','EmitMarkedUU.lean','Audit.lean')]
        tool_pins = [pin(p) for p in tools]
        data_pins = [pin(case_table)]
        result['tool_data'] = data_pins
        python = pin(Path(sys.executable).resolve())
        result.update(tool_sources=tool_pins, python_runtime={'binary':python,'version':sys.version})
        env = dict(os.environ)
        env['LEAN_PATH'] = os.pathsep.join(map(str, [directory/'lib']+paths))
        result['LEAN_PATH'] = env['LEAN_PATH']
        audit_source = here/'Audit.lean'
        imports = build.imports_of(audit_source.read_text())
        need(imports == ['UniformK61.WholeProof'] and all(m in selected for m in imports),
             'Final audit import is outside the accepted build')
        record = run([str(binary),'-j1',str(audit_source)],root,env,destination/'audit.log')
        result['executions'].append(record)
        write_once(destination/'audit_execution.json',record)
        need(record['exit_code'] == 0, 'Exact final theorem type/count audit failed')
        audit = {'source':pin(audit_source), 'execution':record,
                 'axioms':check_axiom_reports((destination/'audit.log').read_text()),
                 'exact_type_checked':True, 'exact_case_count':56723}
        result['final_theorem_audit'] = audit
        write_once(destination/'FINAL_THEOREM_AUDIT.json',audit)
        emissions = [
            ('c','EmitCEntrance.lean',[str(destination/'base.clauses'),str(destination/'c_units.txt')]),
            ('balance','EmitBalanced.lean',[str(destination/'balanced')]),
            ('common','EmitCommon.lean',[str(destination/'common')]),
            ('marked_uu','EmitMarkedUU.lean',[str(destination/'marked_uu')]),
        ]
        for name, emitter, arguments in emissions:
            imports = build.imports_of((here/emitter).read_text())
            need(imports and all(m in selected for m in imports), 'Emitter import is outside the accepted build')
            record = run([str(binary),'-j1','--run',str(here/emitter)]+arguments,
                         root,env,destination/(name+'_emission.log'))
            result['executions'].append(record)
            write_once(destination/(name+'_execution.json'),record)
            need(record['exit_code'] == 0, 'Emitter failed: '+name)
        emitted = [destination/'base.clauses', destination/'c_units.txt']
        emitted += [destination/'balanced'/(owner+'.cnf') for owner in ('UU','UT','TT')]
        emitted += sorted((destination/'common').glob('*.tsv'))
        emitted += sorted((destination/'marked_uu').glob('*.tsv'))
        emission_pins = [pin(path) for path in emitted]
        result['emitted_artifacts'] = emission_pins
        command = [sys.executable,'-I','-B',str(here/'check_all.py'),'--inputs',str(inputs),
                   '--c-base',str(destination/'base.clauses'),'--c-units',str(destination/'c_units.txt'),
                   '--common',str(destination/'common'),'--marked-uu',str(destination/'marked_uu'),
                   '--case-table',str(case_table),
                   '--balance',str(destination/'balanced'),
                   '--output-dir',str(destination/'checks')]
        record = run(command,root,env,destination/'checks.log')
        result['executions'].append(record)
        need(record['exit_code'] == 0, 'Complete input binding failed; see checks.log')
        execution_logs = [entry['log'] for entry in result['executions']]
        for record in (tool_pins+data_pins+input_pins+emission_pins+execution_logs
                       +[python,custody['build_result'],custody['source_manifest']]
                       +custody['module_receipts']+custody['module_logs']):
            need(pin(record['path']) == record, 'Execution input changed: '+record['path'])
        build.check_artifacts(custody['runtime_artifacts'])
        need(build.sha(binary) == compiler['sha256'], 'Lean runtime changed during export')
        manifest = json.loads((root/'SOURCE_MANIFEST.json').read_text())
        build.static_check(root,manifest,json.loads((directory/'BUILD_RESULT.json').read_text())['targets'],False)
        binding = destination/'checks/BINDING_RESULT.json'
        report = json.loads(binding.read_text())
        need(report['status'] == 'PASS_ALL_56723_INPUTS', 'Unexpected whole binding status')
        result.update(status='PASS',cases=56723,binding=pin(binding),
                      scope='Successful current-source Lean build, exact executed emitters/runtime custody, and exhaustive input-byte binding. Serialization and execution are external checks, not kernel-replayed SAT certificates.')
    except Exception as error:
        result['error'] = str(error)
    result['finished_utc'] = datetime.now(timezone.utc).isoformat()
    write_once(destination/'RUN_RESULT.json',result)
    print(json.dumps({k:v for k,v in result.items() if k not in ('build_custody','tool_sources','emitted_artifacts')},indent=2))
    return 0 if result['status'] == 'PASS' else 1


if __name__ == '__main__':
    sys.exit(main())
