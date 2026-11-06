#!/usr/bin/env python3
"""Recompute successful-run CPU time from the complete selected K60 evidence.

Exactly one terminal accepted UNSAT execution is charged per distinct formula
per solver. Earlier attempts are separately reconciled, never relabelled or
removed from the native evidence. No solver, generator or Lean process runs.
"""
import argparse
from collections import Counter
from decimal import Decimal, ROUND_HALF_UP
import gzip
import hashlib
import json
from pathlib import Path
import re
import sqlite3
import sys

sys.dont_write_bytecode = True
import publication_native_evidence as native

SCHEMA = 'K60_SUCCESSFUL_RUN_TIMINGS_1'
TOTAL = 296081
POLICY = ('Successful accepted terminal UNSAT execution CPU time once per selected distinct formula per solver. '
          'Previous TIMEOUT, INTERRUPTED and the preserved reviewed raw ERROR attempt are excluded from headline '
          'times and retained as unsuccessful-attempt overhead. Sleep and elapsed wall time are not CPU time. '
          'The four direct C2 successes are included exactly once per solver.')
FAMILIES = [('A',360),('B',5096),('D/UUU',679),('D/UUT',679),('D/UTU',6576),('D/UTT',6576),
            ('D/TTU',18204),('D/TTT',18204),('E/UUU',2037),('E/UUT',6111),('E/UTT',59184),
            ('E/TTT',163836),('C1 entrance',692),('C2 entrance',7840),('All-five formulas',3),('C2 compatibility',4)]
require = native.require


def decimal_text(value):
    return format(value,'f')


def hours(value):
    return decimal_text((value/Decimal(3600)).quantize(Decimal('0.01'),rounding=ROUND_HALF_UP))


def family_of(key, owner):
    family = key.split('/',1)[0]
    if family == 'e':
        result = 'E/'+owner
    elif family == 'abd':
        result = owner.replace('D_','D/',1) if owner.startswith('D_') else owner
    elif family == 'closure':
        result = {'C1_ENTRANCE':'C1 entrance','C2_ENTRANCE':'C2 entrance'}.get(owner)
        if owner.startswith('BALANCE_ALL_FIVE_'): result = 'All-five formulas'
    elif family == 'balance':
        result = 'C2 compatibility'
    else:
        result = None
    require(result in dict(FAMILIES),'Unknown selected timing family: '+str((key,owner)))
    return result


def cpu_from_log(raw, solver):
    pattern = (rb'^c process-time:.*?([0-9]+(?:\.[0-9]+)?) seconds\s*$' if solver == 'kissat' else
               rb'^c total process time since initialization:\s+([0-9]+(?:\.[0-9]+)?)\s+seconds\s*$')
    values = re.findall(pattern,raw,re.M)
    require(len(values)==1,'Missing or repeated native CPU field for '+solver)
    result = Decimal(values[0].decode())
    require(result.is_finite() and result>=0,'Invalid native CPU time')
    return result


def expected_cases(groups):
    result = {family+'/'+cid:row for family,rows in groups.items() for cid,row in rows.items()}
    require(len(result)==TOTAL,'Incomplete selected timing input boundary')
    require(Counter(family_of(key,row['owner']) for key,row in result.items())==dict(FAMILIES),
            'Wrong selected per-family census')
    return result


def new_bucket():
    return {'successful_runs':0,'unsuccessful_attempts':0,'all_attempts':0,
            'successful_cpu_seconds':Decimal(0),'unsuccessful_cpu_seconds':Decimal(0),'all_attempt_cpu_seconds':Decimal(0)}


def add(bucket, seconds, success):
    bucket['all_attempts'] += 1; bucket['all_attempt_cpu_seconds'] += seconds
    name = 'successful' if success else 'unsuccessful'
    bucket['successful_runs' if success else 'unsuccessful_attempts'] += 1
    bucket[name+'_cpu_seconds'] += seconds


def finish_bucket(bucket):
    require(bucket['successful_runs']+bucket['unsuccessful_attempts']==bucket['all_attempts'],
            'Attempt partition does not reconcile')
    require(bucket['successful_cpu_seconds']+bucket['unsuccessful_cpu_seconds']==bucket['all_attempt_cpu_seconds'],
            'Successful and unsuccessful CPU totals do not reconcile')
    result = {k:(decimal_text(v) if isinstance(v,Decimal) else v) for k,v in bucket.items()}
    for prefix in ('successful','unsuccessful','all_attempt'):
        result[prefix+'_cpu_hours'] = hours(bucket[prefix+'_cpu_seconds'])
    return result


def input_census(accepted):
    groups = {name:{} for name in ('e','abd','closure','balance')}
    for key,row in accepted.items():
        family,cid=key.split('/',1); groups[family][cid]={'sha256':row['input_sha256']}
    return native.selection_digest(groups)


def measure(root, groups, *, cadical_database=None, allow_retired=False):
    """Independent raw-log timing pass; overrides are for pre-import comparison only."""
    root=Path(root).resolve(strict=True); expected=expected_cases(groups)
    manifest=native.read_json(root/'NATIVE_RELEASE.json')
    selected_production={key for key in expected if not key.startswith('balance/')}
    totals={s:new_bucket() for s in ('kissat','cadical')}
    families={name:{s:new_bucket() for s in totals} for name,_ in FAMILIES}
    accepted={s:{} for s in totals}; attempted={s:set() for s in totals}
    statuses={s:Counter() for s in totals}; records={s:{} for s in totals}; direct_counts=Counter()
    watched={}; omitted=set()

    def watch(path):
        path=Path(path); actual=native.pin(path)
        if path.is_relative_to(root):
            require(manifest['files'].get(path.relative_to(root).as_posix())==actual,
                    'Timing source differs from its authenticated capsule pin')
        else:
            require(allow_retired and cadical_database is not None and path==Path(cadical_database).resolve(),
                    'Timing source leaves the selected capsule')
        watched[path]=actual

    def take(solver,key,owner,attempt,status,input_sha,log_sha,compressed,cpu_override=None,returncode=None):
        require(key in expected and owner==expected[key]['owner'] and input_sha==expected[key]['sha256'],
                'Timing record differs from selected formula: '+key)
        require(type(attempt) is int and attempt>=1 and (key,attempt) not in attempted[solver],
                'Duplicate or invalid timing attempt')
        attempted[solver].add((key,attempt))
        require(status in ('UNSAT','TIMEOUT','INTERRUPTED','ERROR'),'Unexpected raw status in timing record')
        raw=gzip.decompress(compressed); require(native.sha(raw)==log_sha,'Full native log hash mismatch')
        lines=raw.splitlines(); successful=status=='UNSAT'
        if successful:
            require(returncode==20 and lines.count(b's UNSATISFIABLE')==1 and not lines.count(b's SATISFIABLE'),
                    'Successful timing lacks exact accepted native UNSAT evidence')
            require(key not in accepted[solver],'More than one successful execution for one selected formula')
        else:
            require(not lines.count(b's SATISFIABLE'),'SAT evidence cannot be treated as timing overhead')
        seconds=cpu_from_log(raw,solver) if cpu_override is None else cpu_override
        require(isinstance(seconds,Decimal) and seconds.is_finite() and seconds>=0,'Invalid measured CPU duration')
        row={'key':key,'attempt':attempt,'input_sha256':input_sha,'log_sha256':log_sha,
             'compressed_log_sha256':native.sha(compressed),'cpu_seconds':decimal_text(seconds),'recorded_status':status}
        records[solver][(key,attempt)]=row
        if successful: accepted[solver][key]=row
        label=family_of(key,owner); add(totals[solver],seconds,successful); add(families[label][solver],seconds,successful)
        statuses[solver][status] += 1

    for family in ('e','abd','closure'):
        path=root/manifest['campaigns'][family]['database']; watch(path)
        db=sqlite3.connect(path.as_uri()+'?mode=ro&immutable=1',uri=True); db.row_factory=sqlite3.Row
        try:
            for item in db.execute('SELECT * FROM attempts ORDER BY case_id,attempt'):
                r=dict(item); take('kissat',family+'/'+r['case_id'],r['owner'],r['attempt'],r['status'],r['input_sha256'],
                                  r['log_sha256'],r['log_gzip'],returncode=r['returncode'])
        finally: db.close()
    path=Path(cadical_database).resolve(strict=True) if cadical_database else root/'cadical/results.sqlite3'
    watch(path); db=sqlite3.connect(path.as_uri()+'?mode=ro&immutable=1',uri=True); db.row_factory=sqlite3.Row
    try:
        for item in db.execute('SELECT * FROM attempts ORDER BY key,attempt'):
            r=dict(item)
            if r['key'] not in selected_production and allow_retired:
                require(r['family']=='closure' and r['owner'] in ('BALANCE_BRACE_15','BALANCE_BRACE_16'),
                        'Unexpected omitted production input')
                omitted.add(r['key']); continue
            require(native.sha(r['log_gzip'])==r['compressed_log_sha256'],'Changed compressed CaDiCaL timing log')
            take('cadical',r['key'],r['owner'],r['attempt'],r['status'],r['input_sha256'],r['log_sha256'],r['log_gzip'],returncode=r['returncode'])
    finally: db.close()
    require(len(omitted)==(720 if allow_retired else 0),'Wrong retired-case timing exclusion')

    for cid,row in sorted(groups['balance'].items()):
        for solver in totals:
            base=root/'experiment/jobs'/(cid+'_'+solver)
            receipt_path=base/'result.json'; log_path=base/'native.log.gz'
            watch(receipt_path); watch(log_path)
            receipt=native.read_json(receipt_path)
            require(receipt['job_id']==cid+'_'+solver and receipt['input_id']==cid and receipt['solver']==solver,
                    'Wrong direct C2 timing receipt')
            require(receipt['status']=='UNSAT' and receipt['input_sha256_before']==receipt['input_sha256_after']==row['sha256'],
                    'Changed direct C2 timing input')
            seconds=Decimal(str(receipt['native_cpu_seconds'])).quantize(Decimal('0.000001'))
            resource=Decimal(str(receipt['user_cpu_seconds']))+Decimal(str(receipt['sys_cpu_seconds']))
            require(abs(seconds-resource)<Decimal('0.000001'),'Direct child CPU accounting mismatch')
            blob=log_path.read_bytes(); require(native.sha(blob)==receipt['log']['gzip_sha256'],'Changed direct compressed log')
            take(solver,'balance/'+cid,row['owner'],1,receipt['status'],row['sha256'],receipt['log']['sha256'],blob,
                 cpu_override=seconds,returncode=receipt['exit_code']); direct_counts[solver]+=1

    solvers={}
    for solver in totals:
        require(set(accepted[solver])==set(expected) and len(accepted[solver])==TOTAL and direct_counts[solver]==4,
                'Missing or extra successful selected execution')
        for (key,attempt),row in records[solver].items():
            require(attempt<=accepted[solver][key]['attempt'],'Attempt follows selected terminal UNSAT execution')
        inputs=input_census(accepted[solver]); success_hash=hashlib.sha256(); history_hash=hashlib.sha256()
        for key,row in sorted(accepted[solver].items()): success_hash.update((json.dumps(row,sort_keys=True,separators=(',',':'))+'\n').encode())
        for key,row in sorted(records[solver].items()): history_hash.update((json.dumps(row,sort_keys=True,separators=(',',':'))+'\n').encode())
        solvers[solver]={**finish_bucket(totals[solver]),'selected_ordered_input_sha256':inputs,
                         'successful_execution_census_sha256':success_hash.hexdigest(),
                         'all_attempt_timing_census_sha256':history_hash.hexdigest(),
                         'recorded_attempt_status_counts':dict(sorted(statuses[solver].items())),
                         'direct_c2_successful_runs':direct_counts[solver]}
    require(solvers['kissat']['selected_ordered_input_sha256']==solvers['cadical']['selected_ordered_input_sha256']==native.selection_digest(groups),
            'Cross-solver successful input identity mismatch')
    result_rows=[]
    for name,cases in FAMILIES:
        row={'family':name,'cases':cases}
        for solver in totals:
            require(families[name][solver]['successful_runs']==cases,'Family successful-run count differs')
            row[solver]=finish_bucket(families[name][solver])
        result_rows.append(row)
    for solver in totals:
        for field in ('successful_cpu_seconds','unsuccessful_cpu_seconds','all_attempt_cpu_seconds'):
            require(sum((Decimal(r[solver][field]) for r in result_rows),Decimal(0))==Decimal(solvers[solver][field]),
                    'Family CPU total does not reconcile')
    for path,record in watched.items(): require(native.pin(path)==record,'Evidence changed during timing calculation')
    return {'solvers':solvers,'families':result_rows}


def derive(root, manifest_sha256, verified_result=None):
    root=Path(root).resolve(strict=True)
    verified=native.verify(root,manifest_sha256) if verified_result is None else verified_result
    require(verified.get('passed') is True and verified.get('full_cadical_campaign_complete') is True and
            verified.get('manifest_sha256')==manifest_sha256 and verified.get('total_cases')==TOTAL,
            'Timings require the complete accepted selected native capsule')
    _,groups=native.selection(root,manifest_sha256)
    result=measure(root,groups)
    require(all(result['solvers'][solver]['selected_ordered_input_sha256']==verified['selected_ordered_input_sha256']
                for solver in ('kissat','cadical')),'Successful execution census differs from native audit')
    require(result['solvers']['kissat']['all_attempt_cpu_seconds']==verified['kissat_native_cpu_seconds'] and
            result['solvers']['cadical']['all_attempt_cpu_seconds']==verified['cadical_native_cpu_seconds'],
            'Independent all-attempt timing totals disagree with the unchanged native receipt')
    require(result['solvers']['kissat']['all_attempts']==verified['kissat_attempts'] and
            result['solvers']['cadical']['all_attempts']==verified['cadical_attempts'],'Attempt totals disagree with native audit')
    return {'schema':SCHEMA,'policy':POLICY,'selected_cases':TOTAL,'native_manifest_sha256':manifest_sha256,
            'selected_ordered_input_sha256':verified['selected_ordered_input_sha256'],
            'timing_tool_sha256':native.pin(Path(__file__).resolve())['sha256'],
            'cpu_sources':{'production':'The unique native process-time field in each authenticated complete log.',
                           'direct_c2':'Captured child user+system CPU resource usage, at microsecond precision; direct receipts unchanged.'},
            'hours_rounding':'Decimal seconds divided by3600, rounded to two decimals with ROUND_HALF_UP; sum seconds before rounding.',
            'existing_all_attempt_fields_changed':False,'solver_calls':0,**result}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root',type=Path,required=True); parser.add_argument('--manifest-sha256',required=True)
    action=parser.add_mutually_exclusive_group(required=True)
    action.add_argument('--output',type=Path); action.add_argument('--verify-report',type=Path)
    args=parser.parse_args(); report=derive(args.root,args.manifest_sha256)
    if args.verify_report:
        require(native.read_json(args.verify_report)==report,'Successful-run timing report differs from recomputed native evidence')
        print(json.dumps({'passed':True,'selected_cases':TOTAL,'native_manifest_sha256':args.manifest_sha256,'solver_calls':0},indent=2))
    else:
        require(not args.output.exists(),'Refusing to overwrite timing evidence')
        with args.output.open('x') as stream: stream.write(json.dumps(report,sort_keys=True,indent=2)+'\n')
        print(json.dumps({'passed':True,'report':str(args.output),'solvers':report['solvers']},indent=2))


if __name__=='__main__':
    try: main()
    except (ValueError,OSError,KeyError,TypeError) as exc:
        print(json.dumps({'passed':False,'error':str(exc)},indent=2),file=sys.stderr);sys.exit(2)
