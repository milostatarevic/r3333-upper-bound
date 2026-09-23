#!/usr/bin/env python3
"""Execute the reviewed eight-step clean-output identity check, without solvers."""
import datetime
import hashlib
import json
import os
import pathlib
import subprocess

Q = pathlib.Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(pathlib.Path(path).read_bytes()).hexdigest()


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def main():
    plan_path = Q / 'g/JOINED_PORTABLE_BINDING_PLAN_001.json'
    plan = json.loads(plan_path.read_text())
    custody_path = Q / 'package_001/checks/clean_build/CLEAN_BUILD_CUSTODY.json'
    custody = json.loads(custody_path.read_text())
    require(custody['status'] == 'PASS', 'Final clean custody is required')
    require(custody['mathematical_modules_compiled'] + custody['established_classification_modules_reused'] == 1809,
            'Final clean closure is incomplete')
    require(custody['source_manifest_sha256'] == sha(Q / 'package_001/SOURCE_MANIFEST.json'), 'Final source manifest drift')
    pins = dict(plan['tool_source_pins'])
    pins[plan['lean_binary']] = plan['lean_binary_sha256']
    # Pin every portable control/record too; execution tools verify archive inputs.
    for p in (Q / 'package_001/reproduce').rglob('*'):
        if p.is_file():
            pins[str(p)] = sha(p)
    for p, wanted in pins.items():
        require(sha(p) == wanted, 'Prepared tool/source drift: ' + p)
    root = pathlib.Path(plan['output_root'])
    root.mkdir()
    logs = root / 'step_logs'
    logs.mkdir()
    env = dict(os.environ, **plan['environment'])
    steps = []
    started = datetime.datetime.now(datetime.timezone.utc).isoformat()
    for step in plan['steps']:
        print('START ' + step['label'], flush=True)
        result = subprocess.run(step['argv'], cwd=plan['working_directory'], env=env,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        log = logs / (step['label'] + '.log')
        log.write_text(result.stdout)
        row = {'label': step['label'], 'exit_code': result.returncode, 'log': str(log), 'log_sha256': sha(log)}
        try:
            receipt, _ = json.JSONDecoder().raw_decode(result.stdout.lstrip())
            row.update(receipt=receipt['receipt'], receipt_sha256=sha(receipt['receipt']),
                       CPU_seconds=receipt['CPU_seconds'], status=receipt['status'])
        except (ValueError, KeyError) as error:
            row['receipt_decode_error'] = repr(error)
        steps.append(row)
        (root / 'RUN_STATE.json').write_text(json.dumps({'started_utc': started, 'steps': steps}, indent=2) + '\n')
        require(result.returncode == 0 and row.get('status') == 'PASS', 'Joined check failed: ' + step['label'])
        print('PASS ' + step['label'], flush=True)
    for p, wanted in pins.items():
        require(sha(p) == wanted, 'Tool/source changed during binding: ' + p)
    result = {'status': 'PASS', 'started_utc': started,
              'finished_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
              'plan_sha256': sha(plan_path), 'clean_custody_sha256': sha(custody_path),
              'source_manifest_sha256': custody['source_manifest_sha256'],
              'cases': {'common': 55016, 'UUQ': 1358, 'C': 456, 'total': 56830},
              'new_SAT_calls': 0, 'certificate_replays': 0,
              'CPU_seconds': sum(r['CPU_seconds'] for r in steps),
              'steps': steps, 'source_and_tool_pins': pins}
    (root / 'RUN_RESULT.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k not in ('steps', 'source_and_tool_pins')}, indent=2))


if __name__ == '__main__':
    main()
