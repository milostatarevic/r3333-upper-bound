#!/usr/bin/env python3
"""Run the entire uniform boundary with both native solvers, without time caps.

Only private, anonymous materializations are temporary. The immutable shared
base, every case's units, before/after digests, commands and full logs are kept.
A stop signal stops admission; already submitted solvers finish naturally.
"""
import argparse
from collections import Counter, defaultdict, deque
from concurrent.futures import ProcessPoolExecutor, wait, FIRST_COMPLETED
import datetime
import fcntl
import gzip
import hashlib
import json
import multiprocessing
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import tempfile
import time

FLOOR = 100 << 30
EXPECTED_COUNTS = {'A': 360, 'B': 5096, 'D_UUU': 679, 'D_UUT': 679,
                   'D_UTU': 6576, 'D_UTT': 6576, 'D_TTU': 18204, 'D_TTT': 18204,
                   'C': 346, 'BALANCE': 3}
EXPECTED_BASE = 'f974e4a1e44ae758ba748fc91838cd820cfb807ed4c09e7ffa5dc661d267565e'
STATE = {}
STOP = False


def need(condition, message):
    if not condition:
        raise ValueError(message)


def digest(stream):
    stream.seek(0)
    h, size = hashlib.sha256(), 0
    for block in iter(lambda: stream.read(1 << 20), b''):
        h.update(block); size += len(block)
    return {'bytes': size, 'sha256': h.hexdigest()}


def pin(path):
    with Path(path).open('rb') as stream:
        return digest(stream)


def utc():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


def write_record(path, record):
    with Path(path).open('x') as stream:
        json.dump(record, stream, sort_keys=True, indent=2)
        stream.write('\n'); stream.flush(); os.fsync(stream.fileno())


def replace_status(path, record):
    temporary = path.with_suffix('.tmp')
    with temporary.open('w') as stream:
        json.dump(record, stream, sort_keys=True, indent=2)
        stream.write('\n'); stream.flush(); os.fsync(stream.fileno())
    os.replace(temporary, path)


def load_inputs(root):
    manifest = json.loads((root/'inputs/MANIFEST.json').read_text())
    expected = manifest['family_counts']
    need(manifest['schema'] == 'UNIFORM_K61_INPUTS_2'
         and manifest['complete_family_counts'] == EXPECTED_COUNTS
         and expected and all(name in EXPECTED_COUNTS and count == EXPECTED_COUNTS[name]
                              for name, count in expected.items())
         and manifest['cases'] == sum(expected.values()), 'Input census mismatch')
    need(pin(root/'inputs/cases.jsonl.gz') == manifest['catalog'], 'Catalog digest mismatch')
    need(pin(root/'inputs/base.clauses') == manifest['base']
         and manifest['base']['sha256'] == EXPECTED_BASE, 'Shared base mismatch')
    rows, counts, seen = [], Counter(), set()
    with gzip.open(root/'inputs/cases.jsonl.gz', 'rt') as stream:
        for text in stream:
            row = json.loads(text)
            key = row['family'], row['case_id']
            need(row['id'] == len(rows) and key not in seen, 'Duplicate/out-of-order case')
            need(row['family'] in expected, 'Unselected input family')
            if row['family'] == 'BALANCE':
                need(row['case_id'] in ('UU', 'UT', 'TT') and row['file'] == f'balanced/{row["case_id"]}.cnf'
                     and row['formula']['variables'] == 13656 and row['formula']['clauses'] == 524462,
                     'Balanced formula dimensions or path')
                need(pin(root/'inputs'/row['file']) == {k: row['formula'][k] for k in ('sha256', 'bytes')},
                     'Balanced formula hash')
            else:
                need(row['formula']['variables'] == 7320
                     and row['formula']['clauses'] == 156770+len(row['units']), 'Formula dimensions')
                need(all(type(x) is int and 0 < abs(x) <= 7320 for x in row['units']), 'Unit range')
                need(not (set(row['units']) & {-u for u in row['units']}), 'Contradictory units')
            rows.append(row); seen.add(key); counts[row['family']] += 1
    need(dict(counts) == expected, 'Incomplete family boundary')
    return rows, (root/'inputs/base.clauses').read_bytes()


def worker_init(root, rows, base, solvers):
    STATE.update(root=Path(root), rows=rows, base=base, solvers=solvers)
    # Parent handles graceful stop; each native child is in its own session.
    # A caught handler resets to SIG_DFL on exec; SIG_IGN would be inherited
    # by the native solver and make a later explicit stop harder to perform.
    signal.signal(signal.SIGINT, ignore_worker_signal)
    signal.signal(signal.SIGTERM, ignore_worker_signal)


def ignore_worker_signal(signum, frame):
    pass


def classify(exit_code, log):
    statuses = re.findall(r'^s\s+(\S+)\s*$', log, re.M)
    if exit_code == 20 and statuses == ['UNSATISFIABLE']:
        return 'UNSAT'
    if exit_code == 10 and statuses == ['SATISFIABLE']:
        return 'SAT'
    if exit_code == 0 and statuses == ['UNKNOWN']:
        return 'UNKNOWN'
    return 'ERROR'


def run_one(job):
    index, solver_name = job
    root, row = STATE['root'], STATE['rows'][index]
    solver = STATE['solvers'][solver_name]
    directory = root/'runs'/solver_name/f'{index:05d}'
    directory.mkdir(parents=True, exist_ok=False)
    start = {'schema': 'UNIFORM_K61_START_1', 'id': index, 'family': row['family'],
             'case_id': row['case_id'], 'solver': solver_name, 'worker_pid': os.getpid(),
             'started_utc': utc(), 'formula': row['formula'], 'solver_identity': solver,
             'time_policy': 'unlimited_CPU_and_wall_default_options'}
    write_record(directory/'START.json', start)
    started = time.time()
    record = dict(start)
    record['status'] = 'ERROR'
    try:
        need(pin(solver['path']) == solver['binary'], 'Solver binary changed before run')
        # TemporaryFile unlinks only the private scratch file it creates. The
        # reproducible input is retained as shared base + catalog unit suffix.
        with tempfile.TemporaryFile(dir=root/'scratch') as source:
            if row['family'] == 'BALANCE':
                with (root/'inputs'/row['file']).open('rb') as retained:
                    shutil.copyfileobj(retained, source)
            else:
                source.write(f'p cnf 7320 {row["formula"]["clauses"]}\n'.encode())
                source.write(STATE['base'])
                source.write(''.join(f'{u} 0\n' for u in row['units']).encode())
            source.flush(); os.fsync(source.fileno())
            expected = {k: row['formula'][k] for k in ('bytes', 'sha256')}
            record['input_before'] = digest(source)
            need(record['input_before'] == expected, 'Input digest mismatch before solver')
            source.seek(0)
            command = [solver['path'], f'/dev/fd/{source.fileno()}']
            record['command'] = command
            with (directory/'solver.log').open('xb') as log:
                native_started = time.time()
                process = subprocess.Popen(command, stdout=log, stderr=subprocess.STDOUT,
                    pass_fds=(source.fileno(),), start_new_session=True)
                metadata_error = None
                try:
                    write_record(directory/'NATIVE_START.json', {'pid': process.pid,
                        'started_utc': utc(), 'command': command, 'input_before': record['input_before']})
                except Exception as error:
                    metadata_error = error
                try:
                    while True:
                        try:
                            _, raw_status, usage = os.wait4(process.pid, 0)
                            break
                        except InterruptedError:
                            continue
                    process.returncode = os.waitstatus_to_exitcode(raw_status)
                finally:
                    # Never abandon an already started child after a record or
                    # wait failure. This wait imposes no deadline or signal.
                    if process.returncode is None:
                        process.wait()
                native_wall = time.time()-native_started
                log.flush(); os.fsync(log.fileno())
            record['input_after'] = digest(source)
            record.update(exit_code=process.returncode, raw_wait_status=raw_status,
                user_CPU_seconds=usage.ru_utime, system_CPU_seconds=usage.ru_stime,
                native_CPU_seconds=usage.ru_utime+usage.ru_stime, native_wall_seconds=native_wall,
                peak_RSS_bytes=usage.ru_maxrss*(1 if sys.platform == 'darwin' else 1024))
            if metadata_error is not None:
                raise metadata_error
            need(record['input_after'] == expected, 'Input changed during solver')
            need(pin(solver['path']) == solver['binary'], 'Solver binary changed during run')
        raw_log = (directory/'solver.log').read_text(errors='replace')
        record['status'] = classify(record['exit_code'], raw_log)
        conflicts = re.findall(r'^c\s+conflicts:\s*([\d,]+)', raw_log, re.M)
        # CaDiCaL can finish during parsing without printing this statistic.
        record['conflicts'] = int(conflicts[-1].replace(',', '')) if conflicts else None
        record['conflicts_reported'] = bool(conflicts)
        record['log'] = pin(directory/'solver.log')
    except Exception as error:
        record['status'] = 'ERROR'
        record['error'] = type(error).__name__+': '+str(error)
    record['completed_utc'] = utc()
    record['job_wall_seconds'] = time.time()-started
    write_record(directory/'RESULT.json', record)
    return {k: record[k] for k in ('id', 'family', 'case_id', 'solver', 'status') } | {
        'native_CPU_seconds': record.get('native_CPU_seconds', 0),
        'result': str((directory/'RESULT.json').relative_to(root))}


def ordered_jobs(rows):
    # Round-robin families expose all owners early; every formula gets exactly
    # the same two default-option runs. Order changes no input or solve policy.
    queues = {name: deque(r['id'] for r in rows if r['family'] == name)
              for name in ('C', 'BALANCE', 'A', 'B', 'D_UUU', 'D_UUT', 'D_UTU', 'D_UTT', 'D_TTU', 'D_TTT')}
    while any(queues.values()):
        for queue in queues.values():
            if queue:
                index = queue.popleft()
                yield index, 'kissat'
                yield index, 'cadical'


def stop_admission(signum, frame):
    global STOP
    STOP = True


def run(root, workers):
    global STOP
    root = root.resolve(strict=True)
    lock = (root/'controller.lock').open('a')
    fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    need(not (root/'CAMPAIGN.json').exists(), 'Existing campaign: preserve it; do not overwrite or replay')
    rows, body = load_inputs(root)
    for name in ('runs', 'scratch', 'tools'):
        (root/name).mkdir(exist_ok=False)
    solvers = {}
    for name, version in (('kissat', '4.0.4'), ('cadical', '3.0.1')):
        original = Path('/opt/homebrew/bin')/name
        target = root/'tools'/name
        shutil.copyfile(original, target); target.chmod(0o555)
        actual = subprocess.check_output([str(target), '--version'], text=True).strip()
        need(actual == version, 'Wrong solver version')
        solvers[name] = {'path': str(target), 'version': version, 'binary': pin(target), 'options': []}
    shutil.copyfile(__file__, root/'tools/uniform_campaign.py')
    generator = Path(__file__).with_name('uniform_k61.py')
    input_manifest = json.loads((root/'inputs/MANIFEST.json').read_text())
    need(pin(generator) == input_manifest['generator'], 'Input generator changed since preparation')
    shutil.copyfile(generator, root/'tools/uniform_k61.py')
    dependencies = input_manifest['generator_dependencies']
    need(set(dependencies) == {'uniform_c.py', 'uniform_balance.py'}, 'Generator dependency census')
    for name, identity in dependencies.items():
        path = generator.with_name(name)
        need(pin(path) == identity, 'Generator dependency changed since preparation')
        shutil.copyfile(path, root/'tools'/name)
    (root/'tools/data').mkdir()
    data_pins = {}
    for name, source in (('c_entrances.json', 'C'), ('balance_anchors.json', 'BALANCE'),
                         ('marked_uu.json', 'D_UU')):
        path = generator.parent/'data'/name
        identity = {k: input_manifest['sources'][source][k] for k in ('sha256', 'bytes')}
        need(pin(path) == identity, 'Generator data changed since preparation')
        shutil.copyfile(path, root/'tools/data'/name)
        data_pins[name] = identity
    manifest = {'schema': 'UNIFORM_K61_CAMPAIGN_2', 'started_utc': utc(), 'controller_pid': os.getpid(),
        'workers': workers, 'jobs': 2*len(rows), 'cases': len(rows),
        'family_counts': input_manifest['family_counts'], 'complete_family_counts': EXPECTED_COUNTS,
        'time_policy': 'unlimited_CPU_and_wall_default_options', 'solvers': solvers,
        'input_manifest': pin(root/'inputs/MANIFEST.json'), 'runner': pin(__file__),
        'generator': pin(generator), 'catalog': input_manifest['catalog'], 'base': input_manifest['base'],
        'generator_dependencies': dependencies, 'generator_data': data_pins,
        'disk_floor_bytes': FLOOR, 'no_old_solver_results_adopted': True}
    write_record(root/'CAMPAIGN.json', manifest)
    for sig in (signal.SIGINT, signal.SIGTERM):
        signal.signal(sig, stop_admission)
    jobs, pending = iter(ordered_jobs(rows)), {}
    exhausted, counts, family_counts, cpu = False, Counter(), defaultdict(Counter), 0.0
    started = time.time()
    context = multiprocessing.get_context('fork')
    with (root/'EVENTS.jsonl').open('x') as events:
        with ProcessPoolExecutor(max_workers=workers, mp_context=context,
                initializer=worker_init, initargs=(root, rows, body, solvers)) as pool:
            while True:
                disk_ok = shutil.disk_usage(root).free >= FLOOR
                while not STOP and disk_ok and not exhausted and len(pending) < workers:
                    try:
                        job = next(jobs)
                    except StopIteration:
                        exhausted = True
                        break
                    pending[pool.submit(run_one, job)] = job
                status = {'updated_utc': utc(), 'state': 'DRAINING' if STOP else
                    'DISK_HOLD' if not disk_ok else 'RUNNING', 'completed': sum(counts.values()),
                    'total': len(rows)*2, 'statuses': dict(counts),
                    'families': {k: dict(v) for k, v in family_counts.items()},
                    'native_CPU_seconds': cpu, 'wall_seconds': time.time()-started,
                    'active': [{'id': j[0], 'solver': j[1], 'family': rows[j[0]]['family'],
                                'case_id': rows[j[0]]['case_id']} for j in pending.values()]}
                replace_status(root/'STATUS.json', status)
                if not pending and (STOP or exhausted):
                    break
                if not pending:
                    time.sleep(10)
                    continue
                done, _ = wait(pending, timeout=10, return_when=FIRST_COMPLETED)
                for future in done:
                    job = pending.pop(future)
                    try:
                        result = future.result()
                    except Exception as error:
                        result = {'id': job[0], 'solver': job[1], 'family': rows[job[0]]['family'],
                            'status': 'ERROR', 'native_CPU_seconds': 0, 'error': repr(error)}
                    counts[result['status']] += 1
                    family_counts[result['family']][result['status']] += 1
                    cpu += result['native_CPU_seconds']
                    events.write(json.dumps(result, sort_keys=True)+'\n'); events.flush(); os.fsync(events.fileno())
                    if result['status'] != 'UNSAT':
                        STOP = True
            retained_ok = (pin(root/'inputs/MANIFEST.json') == manifest['input_manifest']
                and pin(root/'inputs/cases.jsonl.gz') == manifest['catalog']
                and pin(root/'inputs/base.clauses') == manifest['base']
                and pin(root/'tools/uniform_campaign.py') == manifest['runner']
                and pin(root/'tools/uniform_k61.py') == manifest['generator']
                and all(pin(root/'tools'/name) == identity for name, identity in dependencies.items())
                and all(pin(root/'tools/data'/name) == identity for name, identity in data_pins.items())
                and all(pin(root/'inputs'/row['file']) == {k: row['formula'][k] for k in ('sha256', 'bytes')}
                        for row in rows if row['family'] == 'BALANCE'))
            status['retained_inputs_and_tools_unchanged'] = retained_ok
            status['state'] = 'COMPLETE' if (exhausted and retained_ok
                and counts == {'UNSAT': len(rows)*2}) else 'STOPPED'
            status['active'] = []
            replace_status(root/'STATUS.json', status)
            write_record(root/'TERMINAL.json', status)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, required=True)
    parser.add_argument('--workers', type=int, default=12)
    args = parser.parse_args()
    need(1 <= args.workers <= (os.cpu_count() or 1), 'Invalid worker count')
    run(args.root, args.workers)


if __name__ == '__main__':
    main()
