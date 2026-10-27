#!/usr/bin/env python3
"""Independently verify UNIFORM-K61 inputs and the complete two-solver evidence.

Inventory mode checks completed records but never promotes partial coverage.
Full verification requires both solvers for every case in the declared complete
families and a consistent terminal record. Optional rederivation rebuilds every
case from authenticated finite data. Selected-family acceptance is distinguished
from the complete proof census.
"""
import argparse
from collections import Counter, defaultdict
import datetime
import gzip
import hashlib
import json
import math
import os
from pathlib import Path
import re
import tarfile

COUNTS = {'A': 360, 'B': 5096, 'D_UUU': 679, 'D_UUT': 679,
          'D_UTU': 6576, 'D_UTT': 6576, 'D_TTU': 18204, 'D_TTT': 18204,
          'C': 346, 'BALANCE': 3}
BASE_SHA = 'f974e4a1e44ae758ba748fc91838cd820cfb807ed4c09e7ffa5dc661d267565e'
ARCHIVE_SHA = '2b85cac94df0317a532aa823cfea93ac83738093fc854805896943f90d468757'
SOLVERS = {'kissat': '4.0.4', 'cadical': '3.0.1'}
POLICY = 'unlimited_CPU_and_wall_default_options'


def require(condition, message):
    if not condition:
        raise ValueError(message)


def pin(path):
    path = Path(path)
    require(path.is_file() and not path.is_symlink(), f'Not a regular retained file: {path}')
    h, size = hashlib.sha256(), 0
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(1 << 20), b''):
            h.update(block); size += len(block)
    return {'sha256': h.hexdigest(), 'bytes': size}


def read_json(path):
    path = Path(path)
    require(path.is_file() and not path.is_symlink(), f'Not a regular JSON record: {path}')
    return json.loads(path.read_text())


def finite_nonnegative(value, label):
    require(type(value) in (int, float) and math.isfinite(value) and value >= 0,
            f'Invalid {label}')


def utc_time(value):
    stamp = datetime.datetime.fromisoformat(value)
    require(stamp.utcoffset() == datetime.timedelta(0), 'Timestamp must use UTC')
    return stamp


def check_pins(root, campaign, inputs):
    pairs = [
        (root/'inputs/MANIFEST.json', campaign['input_manifest']),
        (root/'inputs/cases.jsonl.gz', campaign['catalog']),
        (root/'inputs/base.clauses', campaign['base']),
        (root/'tools/uniform_campaign.py', campaign['runner']),
        (root/'tools/uniform_k61.py', campaign['generator']),
    ]
    require(inputs['catalog'] == campaign['catalog'] and inputs['base'] == campaign['base'],
            'Input manifest differs from campaign')
    require(inputs['generator'] == campaign['generator'], 'Generator source custody mismatch')
    require(inputs['generator_dependencies'] == campaign['generator_dependencies']
            and set(campaign['generator_dependencies']) == {'uniform_c.py', 'uniform_balance.py'},
            'Generator dependency custody mismatch')
    pairs.extend((root/'tools'/name, identity)
                 for name, identity in campaign['generator_dependencies'].items())
    data_sources = [('c_entrances.json','C'), ('balance_anchors.json','BALANCE')]
    if inputs['sources']['D_UU']['path'] == 'reproduce/data/marked_uu.json':
        data_sources.append(('marked_uu.json','D_UU'))
    else:
        require(inputs['sources']['D_UU']['path'] == 'evidence/D/UUT/full_inputs_000/MANIFEST.json',
                'Unrecognized marked U/U source identity')
    require(set(campaign['generator_data']) == {name for name,_ in data_sources},
            'Generator data census')
    for name, family in data_sources:
        expected = {k: inputs['sources'][family][k] for k in ('sha256', 'bytes')}
        require(campaign['generator_data'][name] == expected, 'Generator data custody mismatch')
        pairs.append((root/'tools/data'/name, expected))
    for path, expected in pairs:
        require(pin(path) == expected, f'Retained pin mismatch: {path}')
    require(set(campaign['solvers']) == set(SOLVERS), 'Wrong solver census')
    for name, version in SOLVERS.items():
        solver = campaign['solvers'][name]
        require(solver['version'] == version and solver['options'] == [], 'Nonuniform solver policy')
        require(Path(solver['path']).name == name, 'Solver path/name mismatch')
        require(pin(root/'tools'/name) == solver['binary'], f'Solver binary mismatch: {name}')


def read_catalog(path, base, expected_counts=COUNTS, selected_families=None):
    """Check the full catalog census and independently hash selected formulas.

    Unselected rows remain authenticated source metadata, never accepted inputs.
    The default selects every family and checks every formula payload.
    """
    selected = set(expected_counts) if selected_families is None else set(selected_families)
    require(selected and selected <= set(expected_counts), 'Invalid selected formula families')
    rows, seen, counts, prefixes = [], set(), Counter(), {}
    with gzip.open(path, 'rt') as stream:
        for text in stream:
            row = json.loads(text)
            key = row['family'], row['case_id']
            require(type(row['id']) is int and row['id'] == len(rows), 'Nonconsecutive case id')
            require(key not in seen and row['family'] in expected_counts, 'Duplicate/unknown case')
            require(type(row['case_id']) is str and row['case_id'], 'Missing case identity')
            if row['family'] not in selected:
                formula = row['formula']
                require(set(formula) == {'sha256','bytes','variables','clauses'}
                        and re.fullmatch(r'[0-9a-f]{64}', formula['sha256'])
                        and all(type(formula[k]) is int and formula[k] > 0
                                for k in ('bytes','variables','clauses')), 'Invalid source formula metadata')
                expected = formula
            elif row['family'] == 'BALANCE':
                require(row['case_id'] in ('UU', 'UT', 'TT')
                        and row['file'] == f'balanced/{row["case_id"]}.cnf', 'Balanced input path')
                file = Path(path).parent/row['file']
                require(not file.parent.is_symlink(), 'Linked balanced input directory')
                expected = {**pin(file), 'variables': 13656, 'clauses': 524462}
                count = 0
                with file.open('rb') as source:
                    require(source.readline() == b'p cnf 13656 524462\n', 'Balanced header')
                    for clause in source:
                        values = list(map(int, clause.split()))
                        require(len(values) >= 2 and values[-1] == 0
                                and all(0 < abs(v) <= 13656 for v in values[:-1]), 'Balanced literal range')
                        count += 1
                require(count == 524462, 'Balanced clause census')
            else:
                units = row['units']
                require(type(units) is list and all(type(v) is int and 0 < abs(v) <= 7320 for v in units),
                        'Invalid physical units')
                require(not (set(units) & {-v for v in units}), 'Contradictory physical units')
                n = len(units)
                if n not in prefixes:
                    header = f'p cnf 7320 {156770+n}\n'.encode()
                    h = hashlib.sha256(header); h.update(base)
                    prefixes[n] = (h, len(header)+len(base))
                h, first_bytes = prefixes[n]
                tail = ''.join(f'{v} 0\n' for v in units).encode()
                digest = h.copy(); digest.update(tail)
                expected = {'sha256': digest.hexdigest(), 'bytes': first_bytes+len(tail),
                            'variables': 7320, 'clauses': 156770+n}
            require(row['formula'] == expected, f'Incorrect formula pin: {key}')
            rows.append({k: row[k] for k in ('id', 'family', 'case_id', 'formula')})
            counts[row['family']] += 1; seen.add(key)
    require(dict(counts) == expected_counts, 'Incomplete input case census')
    return rows


def load_census(root):
    campaign, inputs = read_json(root/'CAMPAIGN.json'), read_json(root/'inputs/MANIFEST.json')
    require(campaign['schema'] == 'UNIFORM_K61_CAMPAIGN_2'
            and inputs['schema'] == 'UNIFORM_K61_INPUTS_2', 'Wrong evidence schema')
    counts = inputs['family_counts']
    require(campaign['complete_family_counts'] == inputs['complete_family_counts'] == COUNTS
            and counts and all(f in COUNTS and n == COUNTS[f] for f, n in counts.items()),
            'Wrong full family boundary or incomplete selected family')
    require(campaign['cases'] == inputs['cases'] == sum(counts.values())
            and campaign['jobs'] == 2*sum(counts.values()), 'Wrong finite boundary')
    require(campaign['family_counts'] == counts, 'Wrong selected family boundary')
    require(inputs['source_archive_sha256'] == ARCHIVE_SHA, 'Wrong source archive')
    require(campaign['time_policy'] == POLICY and campaign['no_old_solver_results_adopted'] is True,
            'Wrong campaign policy')
    utc_time(campaign['started_utc'])
    check_pins(root, campaign, inputs)
    base = (root/'inputs/base.clauses').read_bytes()
    require(hashlib.sha256(base).hexdigest() == BASE_SHA and base.count(b'\n') == 156770,
            'Wrong common K61 base')
    return campaign, inputs, read_catalog(root/'inputs/cases.jsonl.gz', base, counts)


def check_record(directory, expected, solver_name, solver_identity, campaign_started):
    require({p.name for p in directory.iterdir()} ==
            {'START.json','NATIVE_START.json','RESULT.json','solver.log'}, 'Unexpected run artifacts')
    start = read_json(directory/'START.json')
    native = read_json(directory/'NATIVE_START.json')
    result = read_json(directory/'RESULT.json')
    for k in ('id', 'family', 'case_id', 'formula'):
        require(start[k] == result[k] == expected[k], f'Wrong {k}: {directory}')
    require(start['schema'] == result['schema'] == 'UNIFORM_K61_START_1', 'Wrong run schema')
    for k, v in start.items():
        require(result.get(k) == v, f'START/RESULT mismatch for {k}')
    require(start['solver'] == solver_name and start['solver_identity'] == solver_identity,
            'Wrong native solver identity')
    require(start['time_policy'] == POLICY, 'Nonuniform run policy')
    require(type(start['worker_pid']) is int and start['worker_pid'] > 0, 'Missing worker identity')
    require(type(native['pid']) is int and native['pid'] > 0, 'Missing native identity')
    before = {'bytes': expected['formula']['bytes'], 'sha256': expected['formula']['sha256']}
    require(result['input_before'] == result['input_after'] == native['input_before'] == before,
            'Input before/after binding mismatch')
    command = result['command']
    require(command == native['command'] and len(command) == 2
            and command[0] == solver_identity['path']
            and re.fullmatch(r'/dev/fd/\d+', command[1]), 'Nondefault native command')
    require(result['status'] == 'UNSAT' and result['exit_code'] == 20
            and type(result['raw_wait_status']) is int
            and os.waitstatus_to_exitcode(result['raw_wait_status']) == 20,
            'Not a successful native UNSAT run')
    require(pin(directory/'solver.log') == result['log'], 'Log hash mismatch')
    text = (directory/'solver.log').read_bytes().decode(errors='replace')
    require(re.findall(r'^s\s+(\S+)\s*$', text, re.M) == ['UNSATISFIABLE'],
            'Missing, conflicting or repeated native result')
    require(re.findall(r'^c\s+exit\s+(\d+)\s*$', text, re.M) == ['20'], 'Native exit log mismatch')
    require(re.search(r'^c\s+Version\s+'+re.escape(solver_identity['version'])+r'(?:\s|$)', text, re.M),
            'Solver version banner mismatch')
    conflicts = re.findall(r'^c\s+conflicts:\s*([\d,]+)', text, re.M)
    require(type(result['conflicts_reported']) is bool, 'Missing conflict-statistic flag')
    require(result['conflicts_reported'] == bool(conflicts), 'Wrong conflict-statistic flag')
    if conflicts:
        require(type(result['conflicts']) is int
                and result['conflicts'] == int(conflicts[-1].replace(',', '')), 'Conflict-count mismatch')
    else:
        require(result['conflicts'] is None, 'Unreported conflicts must remain null')
    for field in ('user_CPU_seconds', 'system_CPU_seconds', 'native_CPU_seconds',
                  'native_wall_seconds', 'job_wall_seconds'):
        finite_nonnegative(result[field], field)
    require(math.isclose(result['user_CPU_seconds']+result['system_CPU_seconds'],
                         result['native_CPU_seconds'], rel_tol=1e-12, abs_tol=1e-6), 'CPU sum mismatch')
    require(type(result['peak_RSS_bytes']) is int and result['peak_RSS_bytes'] >= 0, 'Invalid wait4 peak RSS')
    require(result['job_wall_seconds']+.05 >= result['native_wall_seconds'], 'Impossible job/native wall times')
    started, native_started, completed = map(utc_time,
        (start['started_utc'], native['started_utc'], result['completed_utc']))
    require(campaign_started <= started <= native_started <= completed, 'Inconsistent run timestamps')
    require(abs((completed-started).total_seconds()-result['job_wall_seconds']) < 2,
            'Job wall/timestamp mismatch')
    # Printed CPU values are rounded and precede final process cleanup, so
    # wait4 may legitimately include additional CPU. Peak RSS text is not used:
    # the retained Kissat macOS build prints an inflated value; wait4 is canonical.
    cpu_text = (re.findall(r'^c\s+process-time:.*?([\d.]+) seconds\s*$', text, re.M)
                if solver_name == 'kissat' else
                re.findall(r'^c\s+total process time since initialization:\s*([\d.]+)\s+seconds', text, re.M))
    if cpu_text:
        require(float(cpu_text[-1]) <= result['native_CPU_seconds']+.1,
                'Printed CPU exceeds wait4 total')
    return result


def rederive(root, archive):
    import uniform_k61 as generator
    campaign, inputs = read_json(root/'CAMPAIGN.json'), read_json(root/'inputs/MANIFEST.json')
    require(pin(Path(generator.__file__)) == campaign['generator'],
            'Rebuild generator differs from retained source')
    for name, identity in campaign['generator_dependencies'].items():
        require(pin(Path(generator.__file__).with_name(name)) == identity, 'Rebuild helper differs')
    sources, pins = generator.load_sources(archive)
    require(pins == inputs['sources'], 'Finite source pins differ')
    count = 0
    with gzip.open(root/'inputs/cases.jsonl.gz', 'rt') as stream:
        for row in generator.cases(sources, inputs['family_counts']):
            saved = json.loads(next(stream))
            expected_row = dict(row)
            if 'current_index' in saved:
                expected_row['current_index'], expected_row['id'] = row['id'], count
            require({k: v for k, v in saved.items() if k != 'formula'} == expected_row,
                    'Finite-data-to-uniform case discrepancy')
            _, expected = generator.formula(row)
            require(saved['formula'] == expected, 'Regenerated formula hash differs')
            count += 1
        require(not stream.read(), 'Catalog has extra cases')
    return count


def verify(root, inventory=False, archive_source=None):
    root = Path(root)
    verification_started = datetime.datetime.now(datetime.timezone.utc).isoformat()
    campaign, inputs, cases = load_census(root)
    started = utc_time(campaign['started_utc'])
    terminal_exists = (root/'TERMINAL.json').exists()
    completed, pending, partial = {}, [], []
    family_counts, solver_counts = defaultdict(Counter), defaultdict(Counter)
    cpu = defaultdict(float); wall = defaultdict(float); peaks = defaultdict(int)
    counts, max_cpu, missing_conflicts = Counter(), {}, 0
    run_root = root/'runs'
    require(run_root.is_dir(), 'Missing run directory')
    for directory in run_root.iterdir():
        require(directory.is_dir() and not directory.is_symlink() and directory.name in SOLVERS,
                f'Unexpected solver directory: {directory}')
        solver = directory.name
        for job in directory.iterdir():
            require(job.is_dir() and not job.is_symlink() and re.fullmatch(r'\d{5}', job.name),
                    f'Unexpected job directory: {job}')
            index = int(job.name)
            require(0 <= index < len(cases), 'Out-of-census job')
            key = solver, index
            require(key not in completed, 'Duplicate solver/case result')
            if not (job/'RESULT.json').exists():
                pending.append([solver,index]); continue
            try:
                result = check_record(job, cases[index], solver, campaign['solvers'][solver], started)
            except json.JSONDecodeError:
                if inventory and not terminal_exists:
                    partial.append([solver,index]); continue
                raise
            except ValueError as error:
                raise ValueError(f'{solver}/{index:05d}: {error}') from error
            completed[key] = result
            family_counts[result['family']][solver] += 1; solver_counts[solver]['UNSAT'] += 1
            counts['UNSAT'] += 1; cpu[solver] += result['native_CPU_seconds']
            wall[solver] += result['native_wall_seconds']
            peaks[solver] = max(peaks[solver],result['peak_RSS_bytes'])
            missing_conflicts += not result['conflicts_reported']
            if solver not in max_cpu or result['native_CPU_seconds'] > max_cpu[solver]['CPU_seconds']:
                max_cpu[solver] = {'id':index,'case_id':result['case_id'],'family':result['family'],
                                   'CPU_seconds':result['native_CPU_seconds']}
    total = 2*len(cases)
    ready = len(completed) == total and not pending and not partial
    status = 'INCOMPLETE'
    if ready and terminal_exists:
        terminal = read_json(root/'TERMINAL.json')
        require(read_json(root/'STATUS.json') == terminal, 'Final status and terminal disagree')
        require(terminal['state'] == 'COMPLETE' and terminal['completed'] == terminal['total'] == total
                and terminal['statuses'] == {'UNSAT':total} and terminal['active'] == []
                and terminal['retained_inputs_and_tools_unchanged'] is True, 'Terminal is not complete')
        require(terminal['families'] == {f:{'UNSAT':2*n} for f,n in inputs['family_counts'].items()},
                'Terminal family census')
        require(math.isclose(terminal['native_CPU_seconds'],sum(cpu.values()),rel_tol=1e-9,abs_tol=1e-5),
                'Terminal CPU total mismatch')
        events = set()
        with (root/'EVENTS.jsonl').open() as stream:
            for line in stream:
                event = json.loads(line);key = event['solver'],event['id']
                require(key not in events and key in completed, 'Duplicate/orphan ledger event')
                result = completed[key]
                require(all(event[k] == result[k] for k in ('id','family','case_id','solver','status','native_CPU_seconds')),
                        'Ledger/result disagreement')
                require(event['result'] == f'runs/{key[0]}/{key[1]:05d}/RESULT.json', 'Wrong ledger result path')
                events.add(key)
        require(events == set(completed), 'Incomplete event ledger')
        check_pins(root,campaign,inputs)
        status = 'PASS'
    rebuilt = rederive(root,archive_source) if archive_source else None
    return {'schema':'UNIFORM_K61_VERIFICATION_1','status':status,'inventory':inventory,
            'verification_started_utc':verification_started,
            'verification_completed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
            'cases':len(cases),'expected_runs':total,'verified_UNSAT_runs':len(completed),
            'complete_proof_census': inputs['family_counts'] == COUNTS,
            'selected_family_counts': inputs['family_counts'],
            'missing_runs':total-len(completed),'pending_directories':len(pending),
            'partially_written_records':len(partial),'statuses':dict(counts),
            'families':{k:dict(v) for k,v in family_counts.items()},
            'solvers':{k:dict(v) for k,v in solver_counts.items()},
            'CPU_seconds':dict(cpu),'summed_native_wall_seconds':dict(wall),
            'peak_RSS_bytes':dict(peaks),'slowest_completed':max_cpu,
            'runs_without_conflicts_statistic':missing_conflicts,'rederived_cases':rebuilt,
            'catalog':campaign['catalog'],'input_manifest':campaign['input_manifest'],
            'verifier':pin(__file__),'new_solver_calls':0}


def pack(root, target, report):
    require(report['status'] == 'PASS' and not report['inventory'], 'Cannot pack partial evidence')
    require(report['complete_proof_census'], 'Selected families are not the complete proof package')
    paths = []
    for name in ('CAMPAIGN.json','TERMINAL.json','EVENTS.jsonl','STATUS.json'):
        paths.append(root/name)
    for name in ('inputs','tools','runs'):
        paths.extend(p for p in (root/name).rglob('*') if p.is_file())
    require(all(not p.is_symlink() for p in paths), 'No evidence symlinks may be packed')
    with target.open('xb') as output:
        with tarfile.open(fileobj=output,mode='w:gz',compresslevel=6) as archive:
            for path in sorted(paths):
                archive.add(path,arcname=str(path.relative_to(root)),recursive=False)
    return pin(target)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root',type=Path,required=True)
    parser.add_argument('--inventory',action='store_true')
    parser.add_argument('--rederive',type=Path,metavar='V1_ARCHIVE')
    parser.add_argument('--archive',type=Path,metavar='NEW_ARCHIVE')
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    require(not(args.inventory and args.archive),'Inventory cannot create an evidence archive')
    try:
        report=verify(args.root,args.inventory,args.rederive)
        if args.archive:
            report['evidence_archive']=pack(args.root,args.archive,report)
    except (ValueError,KeyError,OSError,StopIteration,json.JSONDecodeError) as error:
        report={'schema':'UNIFORM_K61_VERIFICATION_1','status':'ERROR',
                'error':type(error).__name__+': '+str(error),'new_solver_calls':0}
    text=json.dumps(report,indent=2,sort_keys=True)+'\n'
    if args.output:
        with args.output.open('x') as stream:stream.write(text)
    print(text,end='')
    raise SystemExit(0 if report['status']=='PASS' or (args.inventory and report['status']=='INCOMPLETE') else 2)


if __name__=='__main__':main()
