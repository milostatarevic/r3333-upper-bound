#!/usr/bin/env python3
"""Completion-gated CaDiCaL import and passive verification for publication.

No controller, solver, generator, or archived code is run. Finalization calls
only the externally hash-pinned current continuation auditor, after requiring
a completed source campaign, and creates a fresh selected snapshot. Historical
rows (including the reviewed ERROR/-14 record) are never edited. Metadata for
omitted brace rows proves subset custody without retaining their solver logs.
"""
from collections import Counter, defaultdict
from contextlib import contextmanager
from datetime import datetime
from decimal import Decimal
import fcntl
import gzip
import hashlib
import importlib.util
import json
import math
from pathlib import Path
import re
import shutil
import sqlite3
import sys
import uuid

from native_evidence import require, file_pin as pin, sha, read_json

CONTINUATION = 'd308bc60a367ba6ac755564dff852297ed784d617ec85114d0a2b106e28d1cff'
CAMPAIGN = 'a728635090c8421e24946f83eadd6dee20f4d3ffd057f8983f1da0fdd0cfc2a6'
CHECKER = '7fdb3a4d0efc6dfa3ad1dec5153c6d79deb78de2c1cf63b957ca5461262a9da5'
LIMITS = [300,1800,7200,28800,86400]
SOURCE_TOTAL = 296797
SELECTED_PRODUCTION_TOTAL = 296077
COLUMNS = ['key','family','case_id','attempt','owner','input_sha256','catalogue_sha256',
           'native_manifest_sha256','solver_sha256','limit_seconds','started_utc','finished_utc',
           'elapsed_seconds','returncode','status','timed_out','interrupted','command_json',
           'command_sha256','log_sha256','compressed_log_sha256','log_gzip']
CONTROL_NAMES = ('authorization','baseline_audit','baseline_members','baseline_progress','legacy_attempt','source_review')
MEMBERS = {'cadical/campaign.json','cadical/continuation-v2.json','cadical/source-completion-audit.json',
           'cadical/results.sqlite3','cadical/retired-attempt-metadata.jsonl',
           'cadical/runtime/runner.py','cadical/runtime/checker.py'} | {'cadical/controls/'+k for k in CONTROL_NAMES}


def completion_gate(report):
    require(report.get('passed') is True and report.get('completion_claim') is True and
            report.get('requires_attention') is False and report.get('total_cases') == SOURCE_TOTAL and
            report.get('unique_accepted_unsat_cases') == SOURCE_TOTAL and report.get('remaining_cases') == 0 and
            report.get('active_leases') == 0 and not report.get('invalid_attempts_or_histories') and
            not report.get('sat_case_ids') and not report.get('sat_unsat_conflict_ids') and
            report.get('original_history_unchanged') is True and report.get('reviewed_native_timeout_attempts') == 1 and
            type(report.get('attempts_seen')) is int and report['attempts_seen'] >= SOURCE_TOTAL and
            type(report.get('attempts_integrity_checked')) is int and
            report.get('attempts_seen') == report.get('attempts_integrity_checked') and
            report.get('checker',{}).get('sha256') == CHECKER and
            report.get('continuation',{}).get('sha256') == CONTINUATION,
            'CaDiCaL publication requires a fresh complete version2 audit of all 296797 source cases')


def effective_status(raw, row):
    """Independently derive the frozen v2 policy, including its exact alarm signature."""
    lines = Counter(raw.decode('utf-8',errors='replace').splitlines())
    unsat = lines['s UNSATISFIABLE']; sat = lines['s SATISFIABLE']; code = row['returncode']
    if unsat+sat > 1: return 'ERROR'
    if code == -999 and row['interrupted']: return 'ERROR' if sat else 'INTERRUPTED'
    if unsat == 1: return 'UNSAT' if code == 20 else 'ERROR'
    if sat == 1: return 'SAT' if code == 10 else 'ERROR'
    if code in (10,20): return 'ERROR'
    if row['interrupted']: return 'INTERRUPTED'
    if row['timed_out']: return 'TIMEOUT'
    near_cap = row['elapsed_seconds'] >= row['limit_seconds']-3
    if code == 0 and (lines['c UNKNOWN'] or lines['s UNKNOWN']) and near_cap: return 'TIMEOUT'
    if (code == -14 and lines['c UNKNOWN']+lines['s UNKNOWN'] == 1 and lines['c exit 0'] == 1 and
            lines['c raising signal 14 (SIGALRM)'] == 1 and near_cap): return 'TIMEOUT'
    return 'ERROR'


def bounded(row):
    result = {k:v for k,v in row.items() if k != 'log_gzip'}
    result['actual_compressed_log_sha256'] = sha(row['log_gzip'])
    return result


def encoded(row):
    return (json.dumps(row,sort_keys=True,separators=(',',':'))+'\n').encode()


def check_row(row, expected, campaign, origin, legacy):
    require(set(row) == set(COLUMNS) and row['key'] in expected,'Unknown CaDiCaL attempt schema or case')
    family,cid = row['key'].split('/',1); case = expected[row['key']]
    require(row['family'] == family and row['case_id'] == cid and row['owner'] == case['owner'] and
            row['input_sha256'] == case['sha256'] and row['catalogue_sha256'] == campaign['catalogues'][family]['sha256'] and
            row['native_manifest_sha256'] == campaign['capsule']['manifest_sha256'] and
            row['solver_sha256'] == campaign['solver']['executable']['sha256'], 'Changed CaDiCaL attempt identity')
    require(type(row['attempt']) is int and row['attempt'] >= 1 and row['limit_seconds'] in LIMITS and
            type(row['returncode']) is int and row['timed_out'] in (0,1) and row['interrupted'] in (0,1),
            'Invalid CaDiCaL attempt/exit/limit fields')
    elapsed = row['elapsed_seconds']
    require(type(elapsed) in (int,float) and math.isfinite(elapsed) and elapsed >= 0, 'Invalid CaDiCaL elapsed duration')
    start = datetime.fromisoformat(row['started_utc']); end = datetime.fromisoformat(row['finished_utc'])
    require(start.tzinfo is not None and end.tzinfo is not None and end >= start, 'Invalid CaDiCaL timestamps')
    command = [campaign['solver']['executable']['path'],'-t',str(row['limit_seconds']),
               origin+'/active-inputs/'+family+'__'+cid+'.a'+str(row['attempt'])+'.cnf']
    text = json.dumps(command,separators=(',',':'))
    require(row['command_json'] == text and row['command_sha256'] == sha(text.encode()), 'Changed CaDiCaL native command')
    require(type(row['log_gzip']) is bytes and sha(row['log_gzip']) == row['compressed_log_sha256'],
            'Changed compressed CaDiCaL log')
    raw = gzip.decompress(row['log_gzip']); require(sha(raw) == row['log_sha256'],'Changed full CaDiCaL log')
    status = effective_status(raw,row)
    reviewed = (row['key'],row['attempt']) == ('abd/B_s00772',1)
    if reviewed:
        require({k:v for k,v in row.items() if k!='log_gzip'} == legacy and status == 'TIMEOUT',
                'Reviewed raw ERROR row changed or no longer proves an unresolved alarm timeout')
    else:
        require(status == row['status'], 'Recorded CaDiCaL status differs from full native evidence')
    require(status in ('UNSAT','TIMEOUT','INTERRUPTED'),'SAT or unreviewed CaDiCaL error forbids publication')
    values = re.findall(rb'^c total process time since initialization:\s+([0-9]+(?:\.[0-9]+)?)\s+seconds\s*$',raw,re.M)
    require(len(values) == 1,'Missing or repeated CaDiCaL CPU statistic')
    return status,Decimal(values[0].decode()),len(raw)


def check_history(history):
    next_cap = LIMITS[0]
    for number,(attempt,cap,status) in enumerate(history,1):
        require(attempt == number and next_cap is not None and cap == next_cap,'Invalid CaDiCaL retry history')
        if status == 'TIMEOUT':
            index = LIMITS.index(next_cap); next_cap = LIMITS[index+1] if index+1<len(LIMITS) else None
        elif status != 'INTERRUPTED': next_cap = None
    require(history and history[-1][2] == 'UNSAT','Selected CaDiCaL case remains unresolved')


def inspect(store, manifest, groups):
    component = manifest['cadical']; origin = component['origin_directory']
    require(component['members'] == sorted(MEMBERS),'Changed CaDiCaL component member set')
    require(pin(store.path('cadical/campaign.json'))['sha256'] == CAMPAIGN and
            pin(store.path('cadical/continuation-v2.json'))['sha256'] == CONTINUATION,
            'Changed CaDiCaL campaign/continuation identity')
    campaign = read_json(store.path('cadical/campaign.json')); continuation = read_json(store.path('cadical/continuation-v2.json'))
    require(continuation['campaign']['path'] == origin+'/campaign.json' and campaign['jobs'] == 12 and
            campaign['limits_seconds'] == LIMITS and campaign['case_count'] == SOURCE_TOTAL,
            'Changed original CaDiCaL execution policy')
    require(campaign['solver']['executable']['sha256'] == manifest['experiment_solver_pins']['cadical'],
            'Production and direct-exclusion CaDiCaL executables differ')
    controls = {}
    for name in CONTROL_NAMES:
        path = store.path('cadical/controls/'+name)
        require(pin(path) == {k:continuation[name][k] for k in ('sha256','bytes')},'Changed continuation control')
        if name != 'baseline_members': controls[name] = read_json(path)
    for name in ('runner','checker'):
        require(pin(store.path('cadical/runtime/'+name+'.py')) ==
                {k:continuation['runtime'][name][k] for k in ('sha256','bytes')}, 'Changed continuation runtime source')
    report = read_json(store.path('cadical/source-completion-audit.json')); completion_gate(report)
    require(report['campaign']['path'] == origin+'/campaign.json' and report['campaign']['sha256'] == CAMPAIGN,
            'Final audit belongs to a different production campaign')
    expected = {family+'/'+cid:row for family in ('e','abd','closure') for cid,row in groups[family].items()}
    require(len(expected) == SELECTED_PRODUCTION_TOTAL,'Wrong selected production subset')
    omitted = [json.loads(line) for line in store.path('cadical/retired-attempt-metadata.jsonl').read_bytes().splitlines()]
    require(all(r['key'] not in expected and r['family']=='closure' and r['owner'] in ('BALANCE_BRACE_15','BALANCE_BRACE_16')
                and set(r)==(set(COLUMNS)-{'log_gzip'})|{'actual_compressed_log_sha256'} for r in omitted),
            'Omitted CaDiCaL metadata is not restricted to retired brace histories')
    require(len({r['key'] for r in omitted}) == 720,'Incomplete retired CaDiCaL boundary')
    baseline_members = {tuple(json.loads(line)) for line in store.path('cadical/controls/baseline_members').read_bytes().splitlines()}
    require(len(baseline_members)==152732,'Changed continuation baseline membership')
    db = sqlite3.connect(store.path('cadical/results.sqlite3').resolve().as_uri()+'?mode=ro&immutable=1',uri=True)
    db.row_factory = sqlite3.Row; histories = defaultdict(list); rows = []; counts = Counter(); raw_counts=Counter()
    cpu=Decimal(0); log_bytes=0; owner_cpu=defaultdict(Decimal); actual_keys=set()
    try:
        require(db.execute('PRAGMA quick_check').fetchone()[0]=='ok','Corrupt CaDiCaL selected snapshot')
        require([r['name'] for r in db.execute('PRAGMA table_info(attempts)')]==COLUMNS,'Changed CaDiCaL table schema')
        require(dict(db.execute('SELECT key,value FROM metadata')).get('campaign_sha256')==CAMPAIGN,'Changed snapshot metadata')
        require(db.execute('SELECT count(*) FROM leases').fetchone()[0]==0,'Active CaDiCaL leases forbid publication')
        for item in db.execute('SELECT * FROM attempts ORDER BY key,attempt'):
            row=dict(item); status,seconds,size=check_row(row,expected,campaign,origin,controls['legacy_attempt'])
            histories[row['key']].append((row['attempt'],row['limit_seconds'],status)); actual_keys.add(row['key'])
            rows.append(bounded(row)); counts[status]+=1; raw_counts[row['status']]+=1
            cpu+=seconds; owner_cpu[row['owner']]+=seconds; log_bytes+=size
    finally: db.close()
    require(actual_keys==set(expected),'Incomplete selected CaDiCaL coverage')
    for history in histories.values(): check_history(history)
    combined=sorted(rows+omitted,key=lambda r:(r['key'],r['attempt']))
    require(len(combined)==len({(r['key'],r['attempt']) for r in combined}),'Duplicate original CaDiCaL history')
    digest=hashlib.sha256(); baseline=hashlib.sha256(); baseline_count=0
    for row in combined:
        payload=encoded(row); digest.update(payload)
        if (row['key'],row['attempt']) in baseline_members: baseline.update(payload); baseline_count+=1
    require(len(combined)==report['database_snapshot']['rows'] and digest.hexdigest()==
            report['database_snapshot']['ordered_row_and_compressed_log_hash_sha256'],
            'Selected CaDiCaL rows are not the exact subset of the freshly audited complete campaign')
    require(baseline_count==152732 and baseline.hexdigest()==continuation['baseline_snapshot']['ordered_row_and_compressed_log_hash_sha256'],
            'Original CaDiCaL history changed after continuation')
    require(raw_counts['ERROR']==1,'Reviewed raw CaDiCaL error was rewritten or duplicated')
    return {'passed':True,'selected_production_cases':SELECTED_PRODUCTION_TOTAL,'selected_production_attempts':len(rows),
            'effective_attempt_status_counts':dict(counts),'raw_attempt_status_counts':dict(raw_counts),
            'original_history_unchanged':True,'original_source_cases':SOURCE_TOTAL,'retired_source_cases':720,
            'native_log_bytes':log_bytes,'selected_production_cpu_seconds':str(cpu),
            'owner_cpu_seconds':{k:str(v) for k,v in sorted(owner_cpu.items())},
            'source_ordered_row_and_compressed_log_hash_sha256':digest.hexdigest()}


def stopped_completion_gate(campaign):
    progress=read_json(Path(campaign)/'progress.json')
    require(progress.get('controller_status')=='COMPLETE' and progress.get('unique_unsat_cases')==SOURCE_TOTAL and
            not progress.get('active'),'CaDiCaL campaign is not complete; final publication import is refused')


def finalize(root, manifest_sha256, campaign, output):
    import publication_native_evidence as native
    campaign=Path(campaign).absolute(); output=Path(output).absolute(); root=Path(root).absolute()
    stopped_completion_gate(campaign)  # Fast refusal: do not snapshot an ongoing campaign.
    require(campaign.resolve()==campaign and output.resolve()==output and not output.exists(),'Output must be fresh and canonical')
    native.separate_output(output,(root,campaign))
    require(pin(campaign/'continuation-v2.json')['sha256']==CONTINUATION,'Unexpected continuation')
    checker=campaign.parent/'check_results_v2.py'
    require(pin(checker)['sha256']==CHECKER,'Unexpected independent continuation auditor')
    native.verify(root,manifest_sha256)
    manifest=read_json(root/'NATIVE_RELEASE.json'); require('cadical' not in manifest,'This capsule already contains the final CaDiCaL component')
    store,groups=native.selection(root,manifest_sha256)
    selected={family+'/'+cid for family in ('e','abd','closure') for cid in groups[family]}
    with (campaign/'controller.lock').open('rb') as lock:
        fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
        stopped_completion_gate(campaign)
        spec=importlib.util.spec_from_file_location('_accepted_cadical_v2',checker)
        module=importlib.util.module_from_spec(spec); spec.loader.exec_module(module)
        report=module.audit_campaign(campaign,CONTINUATION); completion_gate(report)
        require(pin(checker)['sha256']==CHECKER,'Auditor changed during completion check')
        stage=output.with_name(output.name+'.partial-'+uuid.uuid4().hex[:12]); shutil.copytree(root,stage)
        try:
            def add(source,member,expected=None):
                manifest['files'][member]=native.copy_pinned(source,stage/member,expected)
            add(campaign/'campaign.json','cadical/campaign.json')
            add(campaign/'continuation-v2.json','cadical/continuation-v2.json')
            continuation=read_json(campaign/'continuation-v2.json')
            for name in CONTROL_NAMES:
                record=continuation[name]; add(record['path'],'cadical/controls/'+name,{k:record[k] for k in ('sha256','bytes')})
            for name in ('runner','checker'):
                record=continuation['runtime'][name]; add(record['path'],'cadical/runtime/'+name+'.py',{k:record[k] for k in ('sha256','bytes')})
            native.dump(stage/'cadical/source-completion-audit.json',report)
            manifest['files']['cadical/source-completion-audit.json']=pin(stage/'cadical/source-completion-audit.json')
            src=sqlite3.connect((campaign/'results.sqlite3').as_uri()+'?mode=ro',uri=True); src.row_factory=sqlite3.Row
            dst=sqlite3.connect(stage/'cadical/results.sqlite3'); omitted=[]
            try:
                src.execute('PRAGMA query_only=ON'); src.execute('BEGIN')
                require(src.execute('SELECT count(*) FROM leases').fetchone()[0]==0,'Source acquired new leases')
                for name in ('attempts','metadata','leases'):
                    dst.execute(src.execute('SELECT sql FROM sqlite_master WHERE type=? AND name=?',('table',name)).fetchone()[0])
                dst.executemany('INSERT INTO metadata VALUES (?,?)',src.execute('SELECT key,value FROM metadata'))
                for raw in src.execute('SELECT * FROM attempts ORDER BY key,attempt'):
                    row=dict(raw)
                    if row['key'] in selected:
                        dst.execute('INSERT INTO attempts VALUES ('+','.join('?' for _ in COLUMNS)+')',tuple(row[k] for k in COLUMNS))
                    else:
                        require(row['family']=='closure' and row['owner'] in ('BALANCE_BRACE_15','BALANCE_BRACE_16'),
                                'Cannot omit an unselected non-brace case')
                        omitted.append(bounded(row))
                dst.commit()
            finally: dst.close(); src.rollback(); src.close()
            (stage/'cadical/retired-attempt-metadata.jsonl').write_bytes(b''.join(encoded(r) for r in omitted))
            for member in ('cadical/results.sqlite3','cadical/retired-attempt-metadata.jsonl'): manifest['files'][member]=pin(stage/member)
            manifest['cadical']={'origin_directory':str(campaign),'members':sorted(MEMBERS)}
            manifest['files']=dict(sorted(manifest['files'].items())); native.dump(stage/'NATIVE_RELEASE.json',manifest)
            archived=native.historical.Archive(stage,manifest,pin(stage/'NATIVE_RELEASE.json')['sha256'])
            manifest['verification'],_=native.inspect(archived,manifest)
            native.dump(stage/'NATIVE_RELEASE.json',manifest); digest=pin(stage/'NATIVE_RELEASE.json')['sha256']
            result=native.verify(stage,digest); require(not output.exists(),'Output appeared during finalization'); stage.rename(output)
            return {'passed':True,'root':str(output),'manifest_sha256':digest,'verification':result}
        except Exception as exc:
            native.dump(stage/'FAILED.json',{'passed':False,'error':str(exc)}); raise
