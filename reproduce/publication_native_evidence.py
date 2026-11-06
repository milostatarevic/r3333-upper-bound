#!/usr/bin/env python3
"""Select the published K60 boundary without changing historical solver evidence.

The selected boundary replaces 720 marked-brace formulas by four exact C2
compatibility inputs. Prepare derives a new capsule from the accepted, immutable
Kissat capsule and the completed eight-job experiment. Verify is passive: it
executes no solver, generator, archived Python code, Lean, or subprocess. Export
is a separate, explicit operation which may execute the pinned input generator.
The original campaign headers, commands and retained attempt rows are unchanged.
The full second-solver campaign is deliberately not a completion claim here.
"""
import argparse
from collections import Counter
from datetime import datetime, timezone
from decimal import Decimal
import gzip
import hashlib
import json
import math
from pathlib import Path
import re
import shutil
import sqlite3
import sys
import uuid

import native_evidence as historical
import materialize_input as materializer
import publication_cadical_evidence as second_solver

SCHEMA = 'K60_SELECTED_NATIVE_EVIDENCE_1'
SOURCE_MANIFEST = '089599c2c4ed17524bb73727584391f16f85272facaf283d3923e4938f770d95'
EXPERIMENT_PLAN = '9646e9f012b504996ff9ae5864879fd6c1a76bf24dce69732f464d8958084e14'
EXPERIMENT_AUDIT = '420f21685b31f8675439d1298ffef2c8d209cdf7cb0e3bba1a4ab06025bc6a10'
INPUT_ADMISSION = 'bf6eda11f28a7056efdd79de625cef753a0daddcc62964a339a9effa766d1860'
PREFIX_MANIFEST = '1999e8a27e25fdf080509ca028269801e716171f10aac28c1245847974ecc84d'
OWNERS = ('UU', 'UT', 'TU', 'TT')
COUNTS = {'e':231168, 'abd':56374, 'closure':8535, 'balance':4}
TOTAL = 296081
SOLVERS = {
    'kissat': ('4.0.4', '05d6f3e9c402a1fe8853b0746e384e1b3d1c4a550e255f11daa2461d279aa848'),
    'cadical': ('3.0.1', '601c9fa8ba5d09fd81bb00c89b3e54832f138bccc3422bd8652e8cda4d74d1fa'),
}
LICENSES = {'kissat':{'sha256':'0dbd8c6478aa03f62d720ed2256cf585cb93eba657201be1df217c4e920f162d','bytes':1316},
            'cadical':{'sha256':'9caaed67d8cd9d1c0744ad533b3ed95af756aa54c0402e38746be1f85a4e176c','bytes':1643}}
SELECTION_POLICY = ('The campaign headers and source audits are historical provenance. E and ABD snapshots '
                    'are unchanged. The new closure snapshot contains exactly the original entrance and '
                    'all-five rows, with all 720 brace histories omitted. Omitted metadata and compressed-log '
                    'hashes reconstruct the original accepted row digest; omitted solver log payloads are not retained. '
                    'Four directly refuted C2 prefixes replace the retired formulas.')
TRUST = ('Native exact-input UNSAT outcomes and complete selected attempt/log histories. '
         'No independently checked UNSAT-refutation certificate is claimed. '
         'The conditional Lean reduction and its exact-input bindings are a separate release gate. '
         'Full CaDiCaL completion is claimed only when the separately audited completion component is present.')
require = historical.require
pin = historical.file_pin
sha = historical.sha
read_json = historical.read_json


def dump(path, value):
    Path(path).write_text(json.dumps(value, sort_keys=True, indent=2)+'\n')


def selected_legacy(expected, family):
    """Reject arbitrary subsets: the sole replacement is the complete brace family."""
    if family != 'closure':
        require(family in ('e','abd'), 'Unknown legacy family')
        return dict(expected)
    removed = {k:v for k,v in expected.items() if v['owner'] in ('BALANCE_BRACE_15','BALANCE_BRACE_16')}
    require(Counter(v['owner'] for v in removed.values()) ==
            {'BALANCE_BRACE_15':624,'BALANCE_BRACE_16':96}, 'Wrong retired brace boundary')
    result = {k:v for k,v in expected.items() if k not in removed}
    require(Counter(v['owner'] for v in result.values()) ==
            {'C1_ENTRANCE':692,'C2_ENTRANCE':7840,
             **{'BALANCE_ALL_FIVE_'+o:1 for o in ('UU','UT','TT')}}, 'Wrong selected closure boundary')
    return result


def exact_verdict(raw, code, status):
    lines = raw.splitlines()
    sat = lines.count(b's SATISFIABLE'); unsat = lines.count(b's UNSATISFIABLE')
    if status == 'UNSAT':
        require(code == 20 and (sat,unsat) == (0,1), 'Missing, duplicate or conflicting native UNSAT verdict')
    elif status in ('TIMEOUT','INTERRUPTED'):
        require(code not in (10,20) and (sat,unsat) == (0,0), 'Unresolved attempt has a conclusive verdict')
    else:
        raise ValueError('SAT, ERROR or unknown status forbids selected publication')


def legacy_cpu(raw):
    values = re.findall(rb'^c process-time:.*?([0-9]+(?:\.[0-9]+)?) seconds\s*$', raw, re.M)
    require(len(values) == 1, 'Missing or repeated Kissat process-time statistic')
    return Decimal(values[0].decode())


def selected_history(database, expected, campaign, origin):
    """Audit every retained raw row and complete gzip, including unresolved retries."""
    result = historical.audit_history(database, expected, campaign, origin)
    db = sqlite3.connect(Path(database).resolve().as_uri()+'?mode=ro&immutable=1', uri=True)
    db.row_factory = sqlite3.Row
    total = Decimal(0); owners = {}; previous = {}
    try:
        for row in db.execute('SELECT * FROM attempts ORDER BY case_id,attempt'):
            raw = gzip.decompress(row['log_gzip'])
            exact_verdict(raw, row['returncode'], row['status'])
            old = previous.get(row['case_id'])
            if old:
                require(old['status'] != 'UNSAT', 'Attempt follows a conclusive native result')
                require(row['limit_seconds'] >= old['limit_seconds'], 'Retry decreases the time limit')
            previous[row['case_id']] = {'status':row['status'],'limit_seconds':row['limit_seconds']}
            cpu = legacy_cpu(raw); total += cpu
            owner = row['owner']; owners[owner] = owners.get(owner, Decimal(0))+cpu
    finally:
        db.close()
    result['native_cpu_seconds'] = str(total)
    result['owner_cpu_seconds'] = {k:str(v) for k,v in sorted(owners.items())}
    return result


def bounded_row(row):
    result = {k:v for k,v in row.items() if k != 'log_gzip'}
    result['compressed_log_sha256'] = sha(row['log_gzip'])
    return result


def closure_subset_proof(store, parent, original_expected, selected_expected):
    """Prove byte-preserving row selection against the accepted historical digest."""
    path = store.path('provenance/retired-closure-attempts.jsonl')
    omitted = [json.loads(line) for line in path.read_bytes().splitlines()]
    columns = (set(historical.COLUMNS)-{'log_gzip'})|{'compressed_log_sha256'}
    retired = set(original_expected)-set(selected_expected)
    require(len(omitted) == 720 and {r['case_id'] for r in omitted} == retired,
            'Omission ledger is not the exact retired boundary')
    require(all(set(r) == columns and r['status'] == 'UNSAT' and r['attempt'] == 1 for r in omitted),
            'Malformed retired attempt metadata')
    db = sqlite3.connect(store.path(parent['campaigns']['closure']['database']).resolve().as_uri()+'?mode=ro&immutable=1',uri=True)
    db.row_factory = sqlite3.Row
    try:
        rows = [bounded_row(dict(r)) for r in db.execute('SELECT * FROM attempts')]+omitted
    finally:
        db.close()
    rows.sort(key=lambda r:(r['case_id'],r['attempt']))
    require(len(rows) == len({(r['case_id'],r['attempt']) for r in rows}), 'Duplicate merged original history')
    h = hashlib.sha256()
    for row in rows: h.update((json.dumps(row,sort_keys=True,separators=(',',':'))+'\n').encode())
    old = parent['verification']['closure']
    require(len(rows) == old['attempts'] and h.hexdigest() == old['ordered_row_and_compressed_log_hash_sha256'],
            'Selected closure rows are not an unchanged subset of the accepted historical rows')
    return {'omitted_attempts':720,'original_ordered_row_and_compressed_log_hash_sha256':h.hexdigest()}


def prefix_specs(store):
    origin = str(store.pilot/'balance-simplification-pilot/manifest-pentagon-only.json')
    path = store.get(origin)
    require(pin(path)['sha256'] == PREFIX_MANIFEST, 'Changed compatibility prefix manifest')
    source = read_json(path); rows = source['prefixes']
    require(len(rows) == 4 and {r['id'] for r in rows} == {'C2_ROOT_'+o for o in OWNERS},
            'Wrong direct compatibility owner set')
    result = {}
    for row in rows:
        require(row['id'] == 'C2_ROOT_'+row['owner'], 'Prefix owner differs from ID')
        path = store.checked(origin, row, 'cnf', 'sha256', 'bytes')
        raw = path.read_bytes()
        require(raw.split(b'\n',1)[0] == f'p cnf {row["variables"]} {row["clauses"]}'.encode(),
                'Wrong direct prefix DIMACS header')
        require(len(raw.splitlines()) == row['clauses']+1, 'Wrong direct prefix clause count')
        result[row['id']] = {'owner':row['owner'], 'sha256':row['sha256'],
                            'variables':row['variables'], 'clauses':row['clauses'],
                            'bytes':len(raw), 'member':str(path.relative_to(store.root))}
    return result


def experiment_job(receipt, raw, compressed, inp, solver, job_id, plan, origin):
    """Check original receipt identities and command, never rewrite a solver record."""
    name = job_id.rsplit('_',1)[0]
    require(receipt['job_id'] == job_id and receipt['input_id'] == name and receipt['solver'] == solver,
            'Experiment receipt belongs to a different job')
    require(receipt['command'] == [plan['solvers'][solver]['path'], inp['path']], 'Changed native experiment command')
    require(receipt['launch_command'] == [plan['resume_command'][0], '-B', origin+'/cpu_exec.py',
            '3600', '3605', *receipt['command']], 'Changed CPU-limited experiment launch command')
    for suffix in ('before','after'):
        require(receipt['input_sha256_'+suffix] == inp['sha256'] and
                receipt['solver_sha256_'+suffix] == SOLVERS[solver][1], 'Changed experiment input or executable')
    require(receipt['limit_reason'] is None, 'Experiment terminated at a limit')
    require(receipt['status'] == 'UNSAT', 'Incomplete direct exclusion')
    exact_verdict(raw, receipt['exit_code'], receipt['status'])
    log = receipt['log']; base = origin+'/jobs/'+job_id
    require(log['path'] == base+'/native.log' and log['gzip_path'] == base+'/native.log.gz',
            'Changed original experiment log path')
    require(pin_bytes(raw) == {'sha256':log['sha256'],'bytes':log['bytes']} and
            pin_bytes(compressed) == {'sha256':log['gzip_sha256'],'bytes':log['gzip_bytes']},
            'Changed complete experiment log')
    require(gzip.decompress(compressed) == raw, 'Compressed experiment log differs from retained full log')
    start = datetime.fromisoformat(receipt['started_utc']); end = datetime.fromisoformat(receipt['finished_utc'])
    require(start.tzinfo is not None and end.tzinfo is not None and end >= start, 'Invalid experiment timestamps')
    for field in ('elapsed_seconds','native_cpu_seconds','user_cpu_seconds','sys_cpu_seconds'):
        value = receipt[field]
        require(type(value) in (int,float) and math.isfinite(value) and value >= 0, 'Invalid experiment duration')
    require(abs(receipt['native_cpu_seconds']-receipt['user_cpu_seconds']-receipt['sys_cpu_seconds']) < 1e-7,
            'Native CPU total differs from captured child resource usage')
    require(receipt['native_cpu_seconds'] < 3600 and receipt['elapsed_seconds'] < 10800,
            'UNSAT receipt exceeds experiment limits')
    return {'job_id':job_id,'input_id':name,'solver':solver,'status':'UNSAT',
            'input_sha256':inp['sha256'],'log_sha256':log['sha256'],
            'compressed_log_sha256':log['gzip_sha256'],
            'native_cpu_seconds':receipt['native_cpu_seconds'],'elapsed_seconds':receipt['elapsed_seconds']}


def pin_bytes(raw):
    return {'sha256':sha(raw),'bytes':len(raw)}


def inspect_experiment(store, manifest, prefixes):
    record = manifest['experiment']; origin = record['origin_directory']
    historical.absolute_origin(origin)
    expected_files = {'plan.json':EXPERIMENT_PLAN, 'final-review-audit.json':EXPERIMENT_AUDIT,
                      'input-admission.json':INPUT_ADMISSION}
    for name,digest in expected_files.items():
        require(pin(store.path('experiment/'+name))['sha256'] == digest, 'Changed accepted experiment control')
    plan = read_json(store.path('experiment/plan.json'))
    admission = read_json(store.path('experiment/input-admission.json'))
    audit = read_json(store.path('experiment/final-review-audit.json'))
    require(admission['passed'] is True and admission['owners'] == list(OWNERS), 'Unaccepted direct prefix admission')
    require(audit['all_eight_unsat'] is True and audit['integrity_passed'] is True and not audit['errors'],
            'Experiment lacks complete independent acceptance')
    require(plan['cpu_limit_seconds'] == 3600 and plan['cpu_hard_limit_seconds'] == 3605 and
            plan['wall_limit_seconds'] == 10800 and plan['maximum_experiment_workers'] == 8 and
            plan['maximum_total_sat_workers'] == 12, 'Changed experiment execution policy')
    for name in ('supervise.py','cpu_exec.py','check_experiment.py','input-admission.json','input-admission.txt'):
        records = [p for p in plan['source_pins'] if p['path'] == origin+'/'+name]
        require(len(records) == 1 and pin(store.path('experiment/'+name)) ==
                {k:records[0][k] for k in ('sha256','bytes')}, 'Changed frozen experiment source: '+name)
    require(set(plan['solvers']) == set(SOLVERS), 'Wrong experiment solver set')
    for solver,(version,digest) in SOLVERS.items():
        s = plan['solvers'][solver]
        require(s['version'] == version and s['sha256'] == digest, 'Changed experiment solver identity')
        require(pin(store.path('experiment/tools/'+solver)) == {'sha256':digest,'bytes':s['bytes']},
                'Changed experiment executable bytes')
        license_record = record['solver_licenses'][solver]
        require(license_record['origin'] == str(Path(s['path']).parent.parent/'LICENSE'),
                'Changed solver license origin')
        require(pin(store.path('experiment/tools/'+solver.upper()+'-LICENSE')) == license_record['pin'] == LICENSES[solver],
                'Changed solver license notice')
    inputs = {r['id']:r for r in plan['inputs']}
    require(len(plan['inputs']) == 4 and set(inputs) == set(prefixes), 'Wrong experiment input set')
    for name,inp in inputs.items():
        expected = prefixes[name]
        require(all(inp[k] == expected[k] for k in ('owner','sha256','bytes','variables','clauses')),
                'Experiment used a different full prefix')
        suffix = '/workspace/k60-pilot/balance-simplification-pilot/prefixes/pentagon-only/'+name+'.cnf'
        require(inp['path'].endswith(suffix), 'Experiment input leaves accepted capsule')
    required = [{'id':name+'_'+solver,'input_id':name,'solver':solver}
                for name in inputs for solver in SOLVERS]
    require(plan['jobs'] == required and len(audit['jobs']) == 8, 'Missing or extra direct experiment jobs')
    results = []; totals = {solver:Decimal(0) for solver in SOLVERS}
    for job,accepted in zip(required,audit['jobs']):
        jid = job['id']; prefix = 'experiment/jobs/'+jid+'/'
        result_path = store.path(prefix+'result.json')
        receipt = read_json(result_path)
        require(pin(result_path) == {k:accepted['result'][k] for k in ('sha256','bytes')},
                'Experiment receipt differs from independent audit')
        require(accepted['job_id'] == jid and accepted['status'] == 'UNSAT' and accepted['exit_code'] == 20,
                'Wrong independent job acceptance')
        compressed = store.path(prefix+'native.log.gz').read_bytes()
        raw = gzip.decompress(compressed)
        result = experiment_job(receipt,raw,compressed,inputs[job['input_id']],job['solver'],jid,plan,origin)
        require(all(result[k] == accepted[k] for k in ('native_cpu_seconds','elapsed_seconds','input_id','solver')),
                'Experiment timing/identity differs from independent audit')
        results.append(result)
        # wait4 resource usage has microsecond precision; remove float addition noise
        # only from derived totals, retaining every original receipt byte unchanged.
        totals[job['solver']] += Decimal(str(receipt['native_cpu_seconds'])).quantize(Decimal('0.000001'))
    return {'cases':4,'attempts':8,'jobs':results,'native_cpu_seconds':{k:str(v) for k,v in totals.items()},
            'full_cadical_campaign_complete':False}


def selection_digest(groups):
    h = hashlib.sha256()
    for family in ('e','abd','closure','balance'):
        for cid,row in sorted(groups[family].items()):
            h.update(f'{family}/{cid} {row["sha256"]}\n'.encode())
    return h.hexdigest()


def expected_members(parent, complete=False):
    result = set(parent['files']) | {'provenance/NATIVE_RELEASE-original.json',
             'provenance/retired-closure-attempts.jsonl','tools/materialize_input.py',
             'tools/publication_native_evidence.py','tools/publication_cadical_evidence.py'}
    result.update('experiment/'+name for name in ('plan.json','final-review-audit.json','input-admission.json',
                  'input-admission.txt','supervise.py','cpu_exec.py','check_experiment.py'))
    for owner in OWNERS:
        for solver in SOLVERS:
            result.update('experiment/jobs/C2_ROOT_'+owner+'_'+solver+'/'+name for name in ('result.json','native.log.gz'))
    for solver in SOLVERS:
        result.update(('experiment/tools/'+solver,'experiment/tools/'+solver.upper()+'-LICENSE'))
    if complete: result.update(second_solver.MEMBERS)
    return result


def inspect(store, manifest):
    parent_path = store.path('provenance/NATIVE_RELEASE-original.json')
    require(pin(parent_path)['sha256'] == SOURCE_MANIFEST, 'Changed accepted source capsule manifest')
    parent = read_json(parent_path)
    require(parent['schema'] == historical.SCHEMA and parent['total_cases'] == 296797,
            'Wrong source capsule boundary')
    require(manifest['origins'] == parent['origins'] and manifest['campaigns'] == parent['campaigns'],
            'Original campaign provenance was rewritten')
    require(manifest['source_manifest_sha256'] == SOURCE_MANIFEST and manifest['source_total_cases'] == 296797,
            'Wrong historical source identity')
    require(manifest['total_cases'] == TOTAL and manifest['family_counts'] == COUNTS and
            manifest['retired_brace_cases'] == 720, 'Wrong selected publication boundary')
    require(manifest['selection_policy'] == SELECTION_POLICY, 'Missing or altered selection/provenance policy')
    require(set(manifest['files']) == expected_members(parent,'cadical' in manifest),
            'Missing or additional selected evidence members')
    require(manifest['experiment_solver_pins'] == {k:v[1] for k,v in SOLVERS.items()}, 'Changed experiment solver pins')
    changed = parent['campaigns']['closure']['database']
    for member,original_pin in parent['files'].items():
        require(member in manifest['files'], 'Missing historical input/provenance member')
        if member != changed:
            require(manifest['files'][member] == original_pin, 'Retained historical member changed: '+member)
    for name,module in [('native_evidence.py',historical),('materialize_input.py',materializer),
                        ('publication_cadical_evidence.py',second_solver),
                        ('publication_native_evidence.py',sys.modules[__name__])]:
        require(pin(store.path('tools/'+name)) == pin(module.__file__), 'Current verifier/exporter differs from capsule')
    results = {}; groups = {}
    for family in ('e','abd','closure'):
        spec = manifest['campaigns'][family]
        campaign = read_json(store.path(spec['campaign']))
        original_expected = historical.catalogue(store,family,campaign)
        expected = selected_legacy(original_expected,family); groups[family] = expected
        require(len(expected) == COUNTS[family], 'Incomplete selected legacy input boundary')
        results[family] = selected_history(store.path(spec['database']),expected,campaign,spec['origin_directory'])
        if family != 'closure':
            old = parent['verification'][family]
            require(all(results[family][k] == v for k,v in old.items()), 'Unchanged source family audit differs')
        else:
            results[family]['original_subset_proof'] = closure_subset_proof(store,parent,original_expected,expected)
    prefixes = prefix_specs(store); groups['balance'] = prefixes
    direct = inspect_experiment(store,manifest,prefixes)
    cpu = sum((Decimal(r['native_cpu_seconds']) for r in results.values()), Decimal(0))
    cpu += Decimal(direct['native_cpu_seconds']['kissat'])
    attempts = sum(r['attempts'] for r in results.values())+4
    counts = Counter()
    for r in results.values(): counts.update(r['attempt_status_counts'])
    counts['UNSAT'] += 4
    result = {'passed':True,'total_cases':TOTAL,'unique_accepted_kissat_unsat_cases':TOTAL,
              'selected_ordered_input_sha256':selection_digest(groups),
              'legacy_campaigns':results,'direct_c2':direct,
              'kissat_attempts':attempts,'kissat_attempt_status_counts':dict(counts),
              'kissat_native_cpu_seconds':str(cpu),'kissat_native_cpu_hours':str(cpu/Decimal(3600)),
              'full_cadical_campaign_complete':False,'solver_executed':False,'trust':TRUST}
    require(attempts == 296236 and counts == {'UNSAT':296081,'TIMEOUT':132,'INTERRUPTED':23},
            'Selected complete Kissat history census differs')
    if 'cadical' in manifest:
        second = second_solver.inspect(store,manifest,groups)
        second_cpu = Decimal(second['selected_production_cpu_seconds'])+Decimal(direct['native_cpu_seconds']['cadical'])
        result.update({'cadical_production':second,'full_cadical_campaign_complete':True,
                       'unique_accepted_cadical_unsat_cases':TOTAL,
                       'cadical_attempts':second['selected_production_attempts']+4,
                       'cadical_native_cpu_seconds':str(second_cpu),
                       'cadical_native_cpu_hours':str(second_cpu/Decimal(3600))})
    return result,groups


def verify(root, manifest_sha256):
    manifest = read_json(Path(root)/'NATIVE_RELEASE.json')
    require(manifest.get('schema') == SCHEMA and manifest.get('native_only') is True and manifest.get('trust') == TRUST,
            'Wrong selected native capsule schema or trust statement')
    store = historical.Archive(root,manifest,manifest_sha256)
    result,_ = inspect(store,manifest)
    require(result == manifest['verification'], 'Selected summary differs from authenticated raw evidence')
    return {**result,'manifest_sha256':manifest_sha256}


def filtered_snapshot(source, target, expected, omission_output=None):
    src = sqlite3.connect(Path(source).resolve().as_uri()+'?mode=ro&immutable=1',uri=True)
    dst = sqlite3.connect(target)
    try:
        for name in ('attempts','metadata'):
            ddl = src.execute('SELECT sql FROM sqlite_master WHERE type=? AND name=?',('table',name)).fetchone()[0]
            dst.execute(ddl)
        metadata = list(src.execute('SELECT * FROM metadata'))
        dst.executemany('INSERT INTO metadata VALUES (?,?)',metadata)
        placeholders = ','.join('?' for _ in historical.COLUMNS); removed = 0; omissions = []
        for row in src.execute('SELECT * FROM attempts ORDER BY case_id,attempt'):
            if row[0] in expected:
                dst.execute('INSERT INTO attempts VALUES ('+placeholders+')',row)
            else:
                require(row[2] in ('BALANCE_BRACE_15','BALANCE_BRACE_16') and row[11] == 'UNSAT',
                        'Filtering would omit evidence other than a completed retired brace case')
                removed += 1
                omissions.append(bounded_row(dict(zip(historical.COLUMNS,row))))
        require(removed == 720,'Wrong number of retired brace attempts'); dst.commit()
        if omission_output is not None:
            Path(omission_output).write_text(''.join(json.dumps(r,sort_keys=True,separators=(',',':'))+'\n' for r in omissions))
    finally:
        dst.close(); src.close()


def copy_pinned(source, target, expected=None):
    before = pin(source)
    if expected is not None: require(before == expected, 'Source pin mismatch: '+str(source))
    target.parent.mkdir(parents=True,exist_ok=True)
    with target.open('xb') as out, Path(source).open('rb') as inp:
        shutil.copyfileobj(inp,out,1 << 20)
    require(pin(target) == before == pin(source), 'Source changed while copying: '+str(source))
    return before


def separate_output(output, protected):
    output = Path(output).absolute()
    for root in protected:
        root = Path(root).absolute()
        require(output != root and root not in output.parents and output not in root.parents,
                'Output must be separate from every immutable source capsule, experiment and campaign')


def prepare(source, experiment, output):
    source = Path(source).absolute(); experiment = Path(experiment).absolute(); output = Path(output).absolute()
    require(source.resolve() == source and experiment.resolve() == experiment and output.resolve() == output,
            'Linked input/output roots forbidden')
    require(not output.exists(), 'Output must be a fresh directory')
    separate_output(output,(source,experiment))
    historical.verify(source,SOURCE_MANIFEST)
    parent = read_json(source/'NATIVE_RELEASE.json')
    require(pin(experiment/'plan.json')['sha256'] == EXPERIMENT_PLAN and
            pin(experiment/'final-review-audit.json')['sha256'] == EXPERIMENT_AUDIT and
            pin(experiment/'input-admission.json')['sha256'] == INPUT_ADMISSION, 'Changed completed experiment')
    stage = output.with_name(output.name+'.partial-'+uuid.uuid4().hex[:12]); stage.mkdir(parents=True)
    files = {}; changed = parent['campaigns']['closure']['database']
    try:
        for member,expected in parent['files'].items():
            if member != changed: files[member] = copy_pinned(source/member,stage/member,expected)
        member = 'provenance/NATIVE_RELEASE-original.json'
        files[member] = copy_pinned(source/'NATIVE_RELEASE.json',stage/member)
        original = historical.Archive(source,parent,SOURCE_MANIFEST)
        spec = parent['campaigns']['closure']; campaign = read_json(source/spec['campaign'])
        selected = selected_legacy(historical.catalogue(original,'closure',campaign),'closure')
        ledger = 'provenance/retired-closure-attempts.jsonl'
        filtered_snapshot(source/changed,stage/changed,selected,stage/ledger)
        files[changed] = pin(stage/changed); files[ledger] = pin(stage/ledger)
        for name in ('plan.json','final-review-audit.json','input-admission.json','input-admission.txt',
                     'supervise.py','cpu_exec.py','check_experiment.py'):
            member = 'experiment/'+name; files[member] = copy_pinned(experiment/name,stage/member)
        plan = read_json(experiment/'plan.json')
        for job in plan['jobs']:
            for name in ('result.json','native.log.gz'):
                member = 'experiment/jobs/'+job['id']+'/'+name
                files[member] = copy_pinned(experiment/'jobs'/job['id']/name,stage/member)
        licenses = {}
        for solver,s in plan['solvers'].items():
            member = 'experiment/tools/'+solver
            files[member] = copy_pinned(s['path'],stage/member,{k:s[k] for k in ('sha256','bytes')})
            license_source = Path(s['path']).parent.parent/'LICENSE'
            member = 'experiment/tools/'+solver.upper()+'-LICENSE'
            files[member] = copy_pinned(license_source,stage/member,LICENSES[solver])
            licenses[solver] = {'origin':str(license_source),'pin':files[member]}
        for name,module in [('materialize_input.py',materializer),('publication_native_evidence.py',sys.modules[__name__]),
                            ('publication_cadical_evidence.py',second_solver)]:
            member = 'tools/'+name; files[member] = copy_pinned(module.__file__,stage/member)
        manifest = {'schema':SCHEMA,'native_only':True,'origins':parent['origins'],'campaigns':parent['campaigns'],
                    'source_manifest_sha256':SOURCE_MANIFEST,'source_total_cases':296797,
                    'selection_policy':SELECTION_POLICY,
                    'experiment_solver_pins':{k:v[1] for k,v in SOLVERS.items()},
                    'family_counts':COUNTS,'total_cases':TOTAL,'retired_brace_cases':720,
                    'experiment':{'origin_directory':str(experiment),'solver_licenses':licenses},'files':dict(sorted(files.items())),
                    'created_utc':datetime.now(timezone.utc).isoformat(),'trust':TRUST}
        dump(stage/'NATIVE_RELEASE.json',manifest)
        store = historical.Archive(stage,manifest,pin(stage/'NATIVE_RELEASE.json')['sha256'])
        manifest['verification'],_ = inspect(store,manifest)
        dump(stage/'NATIVE_RELEASE.json',manifest)
        digest = pin(stage/'NATIVE_RELEASE.json')['sha256']; result = verify(stage,digest)
        require(not output.exists(),'Output appeared during preparation'); stage.rename(output)
        return {'passed':True,'root':str(output),'manifest_sha256':digest,'verification':result}
    except Exception as exc:
        dump(stage/'FAILED.json',{'passed':False,'error':str(exc)})
        raise


def selection(root, digest):
    """Authenticate the selected catalogue without replaying all solver logs."""
    manifest = read_json(Path(root)/'NATIVE_RELEASE.json')
    require(manifest.get('schema') == SCHEMA and manifest.get('total_cases') == TOTAL,
            'Expected selected publication capsule')
    store = historical.Archive(root,manifest,digest)
    parent = read_json(store.path('provenance/NATIVE_RELEASE-original.json'))
    require(pin(store.path('provenance/NATIVE_RELEASE-original.json'))['sha256'] == SOURCE_MANIFEST,
            'Wrong selected source identity')
    groups = {}
    for family in ('e','abd','closure'):
        campaign = read_json(store.path(parent['campaigns'][family]['campaign']))
        groups[family] = selected_legacy(historical.catalogue(store,family,campaign),family)
    groups['balance'] = prefix_specs(store)
    require(selection_digest(groups) == manifest['verification']['selected_ordered_input_sha256'],
            'Selected input digest disagreement')
    return store,groups


def find_selected(groups, key):
    require(type(key) is str and key.count('/') == 1, 'Use a selected family/case-ID key')
    family,cid = key.split('/')
    require(family in groups and cid in groups[family], 'Case is not a selected publication input: '+key)
    return family,cid,groups[family][cid]


def export(root, digest, key, output):
    output = Path(output).absolute()
    require(not output.exists() and not output.is_symlink(), 'Refusing to overwrite export')
    require(output.parent.is_dir(), 'Export parent must already exist')
    store,groups = selection(root,digest); family,cid,row = find_selected(groups,key)
    if family == 'balance':
        copy_pinned(store.path(row['member']),output,{'sha256':row['sha256'],'bytes':row['bytes']})
        result = {k:row[k] for k in ('owner','sha256','bytes','variables','clauses')}
        result.update({'output':str(output),'solver_executed':False})
    else:
        with materializer.catalogue(store.root/'workspace',family) as catalogue:
            require(materializer.find_case(catalogue,cid)['sha256'] == row['sha256'],'Generator differs from selection')
            result = materializer.export(catalogue,cid,output)
    return {**result,'case_key':key,'selected_manifest_sha256':digest}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='command',required=True)
    p = sub.add_parser('prepare')
    p.add_argument('--source',type=Path,required=True); p.add_argument('--experiment',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True)
    for name in ('verify','list','export','finalize-cadical'):
        p = sub.add_parser(name); p.add_argument('--root',type=Path,required=True)
        p.add_argument('--manifest-sha256',required=True)
        if name == 'list': p.add_argument('--prefix',default=''); p.add_argument('--limit',type=int,default=20)
        if name == 'export': p.add_argument('--case-key',required=True); p.add_argument('--output',type=Path,required=True)
        if name == 'finalize-cadical': p.add_argument('--campaign',type=Path,required=True); p.add_argument('--output',type=Path,required=True)
    a = parser.parse_args()
    try:
        if a.command == 'prepare': result = prepare(a.source,a.experiment,a.output)
        elif a.command == 'verify': result = verify(a.root,a.manifest_sha256)
        elif a.command == 'export': result = export(a.root,a.manifest_sha256,a.case_key,a.output)
        elif a.command == 'finalize-cadical': result = second_solver.finalize(a.root,a.manifest_sha256,a.campaign,a.output)
        else:
            require(a.limit > 0, 'List limit must be positive')
            _,groups = selection(a.root,a.manifest_sha256)
            keys = [family+'/'+cid for family,rows in groups.items() for cid in sorted(rows)]
            result = {'case_keys':[k for k in keys if k.startswith(a.prefix)][:a.limit],
                      'total_selected_cases':TOTAL,'solver_executed':False}
        print(json.dumps(result,indent=2)); return 0
    except Exception as exc:
        print(json.dumps({'passed':False,'error':str(exc),'solver_executed':False}),file=sys.stderr); return 2


if __name__ == '__main__':
    sys.exit(main())
