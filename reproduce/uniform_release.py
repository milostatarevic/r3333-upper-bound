#!/usr/bin/env python3
"""Verify and package the complete current proof's native and Lean evidence.

Raw native records keep their original local IDs and commands. Only the current
A/B/D, C, and balanced boundaries are proof dependencies. No solver is executed.
Archived scripts are retained as provenance and are never imported or executed.
"""
import argparse
from collections import Counter, defaultdict
import datetime
import gzip
import hashlib
import importlib.util
import io
import json
import math
from pathlib import Path, PurePosixPath
import re
import tarfile

import uniform_verify as native

COUNTS = dict(native.COUNTS)
ABD_COUNTS = {k:v for k,v in COUNTS.items() if k not in ('C','BALANCE')}
OLD_COUNTS = {**ABD_COUNTS, 'C':456}
C_COUNTS, BALANCE_COUNTS = {'C':346}, {'BALANCE':3}
SELECTED_COUNTS = {'abd':ABD_COUNTS, 'c':C_COUNTS, 'balance':BALANCE_COUNTS}
ABD_CASES, CASES, RUNS = 56374, 56723, 113446
AXIOM_NAMES = {'UniformK61.WholeProof.ramsey61','UniformK61.WholeProof.native_case_count'}
STANDARD_AXIOMS = {'propext','Classical.choice','Quot.sound'}
BINDING_TOOLS = {'reproduce/uniform/'+name for name in (
    'run_binding.py','check_all.py','check_common.py','check_c_entrance.py',
    'check_balance.py','check_marked_uu.py','EmitCommon.lean','EmitCEntrance.lean',
    'EmitBalanced.lean','EmitMarkedUU.lean','Audit.lean')}
GENERATOR_DEPENDENCIES = {'uniform_c.py', 'uniform_balance.py'}
GENERATOR_DATA = {'D_UU':'marked_uu.json', 'C':'c_entrances.json',
                  'BALANCE':'balance_anchors.json'}
need, read = native.require, native.read_json


def identity(record):
    return {k:record[k] for k in ('sha256','bytes')}


class Files:
    """Pinned files selected for the fixed release layout, not arbitrary copying."""
    def __init__(self):
        self.entries = {}
        self.watched = {}

    def watch(self, path, expected=None):
        """Retain a custody pin without putting this source in the archive."""
        path = Path(path)
        observed = native.pin(path)
        if expected is not None:
            need(observed == identity(expected), 'Watched file mismatch: '+str(path))
        need(path not in self.watched or self.watched[path] == observed,
             'Watched file changed: '+str(path))
        self.watched[path] = observed
        return observed

    def add(self, path, member, expected=None):
        path, member = Path(path), str(PurePosixPath(member))
        need(member and not member.startswith('/') and '..' not in PurePosixPath(member).parts,
             'Unsafe release member')
        observed = native.pin(path)
        if expected is not None:
            need(observed == identity(expected), 'Retained file mismatch: '+str(path))
        value = (path, observed)
        need(member not in self.entries or self.entries[member] == value, 'Duplicate release member')
        self.entries[member] = value
        return observed

    def unchanged(self):
        for path, expected in list(self.entries.values())+list(self.watched.items()):
            need(native.pin(path) == expected, 'Evidence changed during verification: '+str(path))


def rows_of(inputs, counts, schema, files=None, prefix='inputs', selected_families=None):
    inputs = Path(inputs)
    manifest_pin = native.pin(inputs/'MANIFEST.json')
    manifest = read(inputs/'MANIFEST.json')
    need(manifest['schema'] == schema and manifest['family_counts'] == counts
         and manifest['cases'] == sum(counts.values()), 'Wrong declared input boundary')
    if schema == 'UNIFORM_K61_INPUTS_2':
        need(manifest['complete_family_counts'] == COUNTS, 'Wrong current full boundary')
    need(manifest['source_archive_sha256'] == native.ARCHIVE_SHA, 'Wrong finite source archive')
    need(native.pin(inputs/'cases.jsonl.gz') == manifest['catalog']
         and native.pin(inputs/'base.clauses') == manifest['base']
         and manifest['base']['sha256'] == native.BASE_SHA, 'Input custody mismatch')
    base = (inputs/'base.clauses').read_bytes()
    checked = native.read_catalog(inputs/'cases.jsonl.gz',base,counts,selected_families)
    with gzip.open(inputs/'cases.jsonl.gz','rt') as stream:
        rows = [json.loads(line) for line in stream]
    need(len(rows) == len(checked), 'Input catalog changed while reading')
    for row, check in zip(rows,checked):
        need(all(row[k] == value for k,value in check.items()), 'Input row changed while reading')
    if files is not None:
        for name in ('MANIFEST.json','cases.jsonl.gz','base.clauses'):
            files.add(inputs/name,f'{prefix}/{name}', manifest_pin if name=='MANIFEST.json' else manifest['catalog' if name=='cases.jsonl.gz' else 'base'])
        for row in rows:
            if row['family'] == 'BALANCE' and (selected_families is None or 'BALANCE' in selected_families):
                files.add(inputs/row['file'],f'{prefix}/{row["file"]}',row['formula'])
    return manifest, rows


def source_metadata(root, manifest, schema, counts, files, prefix):
    campaign_pin = native.pin(root/'CAMPAIGN.json')
    campaign = read(root/'CAMPAIGN.json')
    need(campaign['schema'] == schema and campaign['cases'] == sum(counts.values())
         and campaign['jobs'] == 2*sum(counts.values())
         and campaign['family_counts'] == counts, 'Wrong source campaign census')
    need(campaign['time_policy'] == native.POLICY
         and campaign['no_old_solver_results_adopted'] is True, 'Wrong source native policy')
    for key,name in (('input_manifest','inputs/MANIFEST.json'),('catalog','inputs/cases.jsonl.gz'),
                     ('base','inputs/base.clauses'),('runner','tools/uniform_campaign.py'),
                     ('generator','tools/uniform_k61.py')):
        files.add(root/name,f'{prefix}/{name}',campaign[key])
    need(manifest['generator'] == campaign['generator'] and manifest['catalog'] == campaign['catalog']
         and manifest['base'] == campaign['base'], 'Source manifest/campaign mismatch')
    need(set(campaign['solvers']) == set(native.SOLVERS), 'Wrong solver census')
    for name,version in native.SOLVERS.items():
        solver = campaign['solvers'][name]
        need(solver['version'] == version and solver['options'] == []
             and Path(solver['path']).name == name, 'Wrong solver command policy')
        files.add(root/'tools'/name,f'{prefix}/tools/{name}',solver['binary'])
    if schema == 'UNIFORM_K61_CAMPAIGN_2':
        need(campaign['complete_family_counts'] == COUNTS, 'Wrong source full family boundary')
        native.check_pins(root,campaign,manifest)
        for name,pin in campaign['generator_dependencies'].items():
            files.add(root/'tools'/name,f'{prefix}/tools/{name}',pin)
        for name,pin in campaign['generator_data'].items():
            files.add(root/'tools/data'/name,f'{prefix}/tools/data/{name}',pin)
    for name in ('CAMPAIGN.json','TERMINAL.json','STATUS.json','EVENTS.jsonl'):
        files.add(root/name,f'{prefix}/{name}',campaign_pin if name=='CAMPAIGN.json' else None)
    return campaign


def row_identity(row):
    return {k:row[k] for k in ('family','case_id','formula','file' if row['family']=='BALANCE' else 'units')}


def selected_source_rows(rows, group):
    selected = [row for row in rows if row['family'] in SELECTED_COUNTS[group]]
    need(dict(Counter(row['family'] for row in selected)) == SELECTED_COUNTS[group],
         'Incomplete selected source boundary')
    need(all(type(row['id']) is int and 0 <= row['id'] < len(rows)
             and rows[row['id']] == row for row in selected), 'Source local index changed')
    return selected


def select_source(current, sources):
    index = current['id']
    group, first = (('abd',0) if index < ABD_CASES else
                    ('c',ABD_CASES) if index < ABD_CASES+346 else ('balance',ABD_CASES+346))
    need(type(index) is int and first <= index < first+sum(SELECTED_COUNTS[group].values())
         and current['family'] in SELECTED_COUNTS[group], 'Current source range mismatch')
    source = sources[group][index-first]
    need('current_index' not in source or source['current_index'] == index,
         'Source local/global index mapping changed')
    need(row_identity(current) == row_identity(source), 'Current/source formula mismatch')
    return group, source


def source_ledger(root, rows, campaign):
    """Authenticate the complete source ledger without adopting unselected runs."""
    terminal = read(root/'TERMINAL.json')
    total = 2*len(rows)
    need(read(root/'STATUS.json') == terminal and terminal['state'] == 'COMPLETE'
         and terminal['completed'] == terminal['total'] == total
         and terminal['statuses'] == {'UNSAT':total} and terminal['active'] == []
         and terminal['retained_inputs_and_tools_unchanged'] is True,
         'Source is incomplete')
    need(terminal['families'] == {f:{'UNSAT':2*n} for f,n in campaign['family_counts'].items()},
         'Source terminal family census')
    events, cpu = {}, 0.0
    with (root/'EVENTS.jsonl').open() as stream:
        for line in stream:
            event = json.loads(line)
            key = event['solver'], event['id']
            need(key[0] in native.SOLVERS and type(key[1]) is int and 0 <= key[1] < len(rows)
                 and key not in events, 'Duplicate or out-of-census source event')
            row = rows[key[1]]
            need(all(event[k] == row[k] for k in ('id','family','case_id'))
                 and event['status'] == 'UNSAT'
                 and event['result'] == f'runs/{key[0]}/{key[1]:05d}/RESULT.json'
                 and type(event['native_CPU_seconds']) in (int,float)
                 and math.isfinite(event['native_CPU_seconds']) and event['native_CPU_seconds'] >= 0,
                 'Invalid source event')
            events[key] = event; cpu += event['native_CPU_seconds']
    need(len(events) == total and math.isclose(terminal['native_CPU_seconds'],cpu,
         rel_tol=1e-9,abs_tol=1e-5), 'Incomplete source ledger or CPU disagreement')
    return events


def current_input_sources(current, old, c_source, balance_source, files, tools=None):
    """Pin the current constructor independently of the frozen native tools.

    Native acceptance below compares every ordered formula with its actual
    solved input. It does not infer formula identity from constructor identity.
    """
    tools = Path(tools) if tools is not None else Path(__file__).resolve().parent
    expected_sources = set(old['sources']) | {'BALANCE'}
    need(set(current['sources']) == expected_sources == set(c_source['sources'])
         == set(balance_source['sources']),
         'Unexpected current finite-source census')
    need({k:v for k,v in old['sources'].items() if k not in ('C','D_UU')} ==
         {k:v for k,v in current['sources'].items() if k not in GENERATOR_DATA},
         'ABD finite-source pins changed')
    for source in (c_source,balance_source):
        need({k:v for k,v in source['sources'].items() if k!='D_UU'} ==
             {k:v for k,v in current['sources'].items() if k!='D_UU'},
             'C/balance finite-source pins changed')
    need(set(current['generator_dependencies']) == GENERATOR_DEPENDENCIES,
         'Unexpected current generator dependency census')
    files.watch(tools/'uniform_k61.py', current['generator'])
    files.add(tools/'uniform_k61.py', 'current/tools/uniform_k61.py', current['generator'])
    for name, pin in current['generator_dependencies'].items():
        files.watch(tools/name, pin)
        files.add(tools/name, 'current/tools/'+name, pin)
    for family, name in GENERATOR_DATA.items():
        pin = current['sources'][family]
        need(pin['path'] == 'reproduce/data/'+name, 'Unexpected current generator data path')
        files.watch(tools/'data'/name, pin)
        files.add(tools/'data'/name, 'current/tools/data/'+name, pin)
    data = read(tools/'data/marked_uu.json')
    need(data['schema'] == 'UNIFORM_K61_MARKED_UU_DATA_1'
         and data['provenance']['source_archive_sha256'] == native.ARCHIVE_SHA
         and data['provenance']['source_manifest'] == old['sources']['D_UU'],
         'Marked case-table source provenance differs')
    for source in (c_source,balance_source):
        need(source['sources']['D_UU'] in (current['sources']['D_UU'],old['sources']['D_UU']),
             'Marked case-table source provenance differs')


def inspect_native(inputs, abd, c_source, balance_source, files, selected_layout=False):
    inputs = Path(inputs)
    im, current = rows_of(inputs,COUNTS,'UNIFORM_K61_INPUTS_2',files)
    roots = dict(zip(('abd','c','balance'),map(Path,(abd,c_source,balance_source))))
    manifests, catalogs, campaigns, selections, ledgers = {}, {}, {}, {}, {}
    for group,root in roots.items():
        declared = read(root/'inputs/MANIFEST.json')
        schema, counts = declared['schema'], declared['family_counts']
        need((schema == 'UNIFORM_K61_INPUTS_1' and group == 'abd' and counts == OLD_COUNTS)
             or (schema == 'UNIFORM_K61_INPUTS_2' and counts
                 and all(f in COUNTS and n == COUNTS[f] for f,n in counts.items())),
             'Wrong source input boundary')
        manifests[group], catalogs[group] = rows_of(root/'inputs',counts,schema,files,
            f'sources/{group}/inputs',SELECTED_COUNTS[group])
        campaigns[group] = source_metadata(root,manifests[group],
            'UNIFORM_K61_CAMPAIGN_'+schema.rsplit('_',1)[1],counts,files,f'sources/{group}')
        selections[group] = selected_source_rows(catalogs[group],group)
        ledgers[group] = source_ledger(root,catalogs[group],campaigns[group])
    current_input_sources(im,manifests['abd'],manifests['c'],manifests['balance'],files)
    for solver in native.SOLVERS:
        first = campaigns['abd']['solvers'][solver]
        need(all(all(campaigns[group]['solvers'][solver][k] == first[k]
                     for k in ('binary','version','options')) for group in roots),
             'Solver identity differs across sources')
    for group,root in roots.items():
        need({p.name for p in (root/'runs').iterdir()}==set(native.SOLVERS), 'Unexpected solver directories')
        for name in native.SOLVERS:
            directory = root/'runs'/name
            need(directory.is_dir() and not directory.is_symlink(), 'Missing native source directory')
            names = {p.name for p in directory.iterdir()}
            expected = {f'{row["id"]:05d}' for row in selections[group]}
            allowed = expected if selected_layout else {f'{row["id"]:05d}' for row in catalogs[group]}
            need(expected <= names <= allowed, 'Missing or extraneous native source jobs')
    cpu,peak,counts,families = defaultdict(float),defaultdict(int),Counter(),defaultdict(Counter)
    ordered = hashlib.sha256()
    for index,row in enumerate(current):
        need(row['id'] == index, 'Current case order changed')
        group,source = select_source(row,selections)
        campaign,root = campaigns[group],roots[group]
        expected = {k:source[k] for k in ('id','family','case_id','formula')}
        for solver in native.SOLVERS:
            relative = f'runs/{solver}/{source["id"]:05d}'
            directory = root/relative
            need(directory.is_dir() and not directory.is_symlink(), 'Linked or missing native record directory')
            for name in ('START.json','NATIVE_START.json','RESULT.json','solver.log'):
                files.add(directory/name,f'sources/{group}/{relative}/{name}')
            result = native.check_record(directory,expected,solver,campaign['solvers'][solver],
                                         native.utc_time(campaign['started_utc']))
            event = ledgers[group][solver,source['id']]
            need(all(event[k] == result[k] for k in
                     ('id','family','case_id','solver','status','native_CPU_seconds')),
                 'Selected ledger/result disagreement')
            cpu[solver] += result['native_CPU_seconds']
            peak[solver] = max(peak[solver],result['peak_RSS_bytes'])
            counts[solver] += 1; families[row['family']][solver] += 1
        ordered.update((row['family']+'\t'+row['case_id']+'\t'+row['formula']['sha256']+'\n').encode())
    need(len(current)==CASES and dict(counts)=={s:CASES for s in native.SOLVERS}, 'Incomplete current native union')
    return {'schema':'UNIFORM_K61_CURRENT_NATIVE_1','status':'PASS_NATIVE_CURRENT_56723',
            'cases':CASES,'native_runs':RUNS,'family_counts':COUNTS,
            'families':{k:dict(v) for k,v in families.items()},'UNSAT':RUNS,'SAT':0,'UNKNOWN':0,'errors':0,
            'CPU_seconds':dict(cpu),'peak_RSS_bytes':dict(peak),
            'catalog':native.pin(inputs/'cases.jsonl.gz'),'input_manifest':native.pin(inputs/'MANIFEST.json'),
            'catalog_order_case_hashes_sha256':ordered.hexdigest(),
            'source_groups':{g:{'local_indices_sha256':hashlib.sha256(
                                ','.join(str(r['id']) for r in selections[g]).encode()).hexdigest(),
                                'local_count':len(selections[g]),
                                'current_first':0 if g=='abd' else ABD_CASES if g=='c' else ABD_CASES+346}
                             for g in roots},
            'no_native_records_rewritten':True,'new_solver_calls':0}


def relative_record(record, origin):
    path = PurePosixPath(record['path'])
    need('..' not in path.parts, 'Unsafe recorded path')
    try:
        return path.relative_to(PurePosixPath(str(origin)))
    except ValueError as error:
        raise ValueError('Recorded path escapes its declared source root') from error


def check_axioms(text):
    pattern = re.compile(r"'([^'\n]+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)")
    reports, end = {}, 0
    for match in pattern.finditer(text):
        need(not text[end:match.start()].strip(), 'Unexpected theorem audit output')
        name = match.group(1)
        axioms = [] if not match.group(2) else [a.strip() for a in match.group(2).split(',')]
        need(name in AXIOM_NAMES and name not in reports and len(axioms)==len(set(axioms))
             and set(axioms)<=STANDARD_AXIOMS, 'Unexpected theorem or axiom dependency')
        reports[name] = axioms; end = match.end()
    need(not text[end:].strip() and set(reports)==AXIOM_NAMES, 'Incomplete final theorem audit')
    return reports


def binding_tools(formal, origin, records, files):
    paths = [relative_record(record,origin) for record in records]
    need(len(paths)==len(set(paths)) and set(map(str,paths))==BINDING_TOOLS,
         'Binding tool paths must be the exact current set')
    for relative,record in zip(paths,records):
        need(record['path']==str(origin/relative), 'Noncanonical binding tool path')
        files.watch(formal/relative,record)
        files.add(formal/relative,'math/tools/'+str(relative),record)


def binding_data(records, inputs, files):
    """Authenticate the explicit case-index table used by the Lean/input join."""
    need(len(records) == 1, 'Exactly one marked case-index table required')
    record = records[0]
    need(Path(record['path']).is_absolute() and Path(record['path']).name == 'marked_uu.json',
         'Unexpected marked case-index table path')
    expected = read(Path(inputs)/'MANIFEST.json')['sources']['D_UU']
    need(expected['path'] == 'reproduce/data/marked_uu.json'
         and identity(record) == identity(expected), 'Binding case-table pin mismatch')
    table = Path(__file__).resolve().parent/'data/marked_uu.json'
    files.watch(table, record)
    files.add(table, 'current/tools/data/marked_uu.json', record)
    return record


def inspect_math(formal, manifest_path, build, binding, inputs, files, live=False):
    formal, manifest_path, build, binding, inputs = (
        Path(p).resolve() for p in (formal,manifest_path,build,binding,inputs))
    mp = files.add(manifest_path,'math/SOURCE_MANIFEST.json')
    files.watch(formal/'SOURCE_MANIFEST.json',mp)
    bp = files.add(build/'BUILD_RESULT.json','math/build/BUILD_RESULT.json')
    rp = files.add(binding/'RUN_RESULT.json','math/binding/RUN_RESULT.json')
    manifest, result, run = read(manifest_path),read(build/'BUILD_RESULT.json'),read(binding/'RUN_RESULT.json')
    modules = manifest['modules']
    expected_sources = {formal/row['path'] for row in modules.values()}
    need(set((formal/'src').rglob('*.lean'))==expected_sources, 'Current Lean source census differs')
    controls = manifest['files']
    if isinstance(controls,dict):
        controls = [dict(value,path=key) for key,value in controls.items()]
    data = manifest['data']
    data = list(data.values()) if isinstance(data,dict) else data
    for row in list(modules.values())+list(data)+list(controls):
        observed = files.watch(formal/row['path'])
        need('sha256' in row and all(observed[k]==row[k] for k in ('sha256','bytes') if k in row),
             'Current mathematical source/data pin mismatch')
    need(result['status']=='PASS' and result['baseline_project_artifacts_reused'] is False
         and result['new_solver_calls']==0 and not result['failures'] and not result['pending']
         and result['interrupted'] is False and result['manifest_sha256']==mp['sha256'],
         'Completed fresh source-only mathematical build required')
    need(result['selected_modules']==len(modules) and len(result['completed'])==len(modules)
         and set(result['completed'])==set(modules) and set(result['targets'])==set(manifest['roots'])
         and 'UniformK61.WholeProof' in modules, 'Incomplete full mathematical source closure')
    need(run['schema']=='UNIFORM_K61_FRESH_BUILD_BINDING_1' and run['status']=='PASS'
         and run['cases']==CASES and run['new_solver_calls']==0 and 'error' not in run,
         'Successful complete current fresh binding required')
    custody = run['build_custody']
    need(identity(custody['source_manifest'])==mp and identity(custody['build_result'])==bp
         and custody['selected_modules']==len(modules) and custody['compiler']==result['compiler'],
         'Binding used a different mathematical build')
    origin_build = PurePosixPath(custody['build_result']['path']).parent
    origin_formal = PurePosixPath(custody['source_manifest']['path']).parent
    origin_binding = PurePosixPath(run['binding']['path']).parent.parent
    receipts = {str(relative_record(p,origin_build)):p for p in custody['module_receipts']}
    logs = {str(relative_record(p,origin_build)):p for p in custody['module_logs']}
    need(len(receipts)==len(custody['module_receipts'])==len(modules)
         and len(logs)==len(custody['module_logs'])==len(modules), 'Duplicate or incomplete module custody')
    runtime = {p['path']:identity(p) for p in custody['runtime_artifacts']}
    for name,row in modules.items():
        recname,logname = f'modules/{name}/receipt.json',f'modules/{name}/lean.log'
        files.add(build/recname,'math/build/'+recname,receipts[recname])
        files.add(build/logname,'math/build/'+logname,logs[logname])
        receipt = read(build/recname)
        need(receipt['status']=='PASS' and receipt['exit_code']==0 and receipt['module']==name
             and receipt['source']==row and receipt['compiler_sha256']==result['compiler']['sha256']
             and receipt['log_sha256']==logs[logname]['sha256'], 'Invalid mathematical module receipt: '+name)
        artifact = str(origin_build/'lib'/Path(name.replace('.','/')).with_suffix('.olean'))
        need(runtime[artifact]=={'sha256':receipt['artifact_sha256'],'bytes':receipt['artifact_bytes']},
             'Module/library identity mismatch')
        for item in receipt['import_artifacts']:
            need(runtime[item['path']]==identity(item), 'Imported artifact custody mismatch')
    binding_tools(formal,origin_formal,run['tool_sources'],files)
    case_table = binding_data(run['tool_data'],inputs,files)
    if live:
        # This is the CURRENT repository tool already matched to the fresh
        # execution receipt. No tool under either native source is executed.
        driver = formal/'reproduce/uniform/run_binding.py'
        spec = importlib.util.spec_from_file_location('_current_uniform_binding',driver)
        module = importlib.util.module_from_spec(spec); spec.loader.exec_module(module)
        *_, observed = module.inspect_build(formal,build)
        need(observed==custody, 'Live accepted compiler/library custody changed')
        for record in run['emitted_artifacts']:
            relative = relative_record(record,origin_binding)
            need(native.pin(binding/relative)==identity(record), 'Raw binding emission changed')
    input_records = run['native_inputs']
    manifests = [p for p in input_records if Path(p['path']).name=='MANIFEST.json']
    need(len(manifests)==1, 'Ambiguous binding input root')
    origin_inputs = PurePosixPath(manifests[0]['path']).parent
    for record in input_records:
        relative = relative_record(record,origin_inputs)
        files.add(inputs/relative,'inputs/'+str(relative),record)
    audit = read(binding/'FINAL_THEOREM_AUDIT.json')
    need(audit==run['final_theorem_audit'] and audit['exact_type_checked'] is True
         and audit['exact_case_count']==CASES, 'Wrong exact final theorem/type boundary')
    need(identity(audit['source'])==native.pin(formal/'reproduce/uniform/Audit.lean'), 'Wrong final audit source')
    files.add(binding/'audit.log','math/binding/audit.log',audit['execution']['log'])
    need(check_axioms((binding/'audit.log').read_text())==audit['axioms'], 'Axiom audit disagreement')
    need(len(run['executions'])==6 and all(p['exit_code']==0 for p in run['executions']),
         'Incomplete audit, four-emitter, and whole-binding execution set')
    for execution in run['executions']:
        relative = relative_record(execution['log'],origin_binding)
        files.add(binding/relative,'math/binding/'+str(relative),execution['log'])
    files.add(binding/'checks/BINDING_RESULT.json','math/binding/checks/BINDING_RESULT.json',run['binding'])
    joined = read(binding/'checks/BINDING_RESULT.json')
    need(joined['status']=='PASS_ALL_56723_INPUTS' and joined['cases']==CASES
         and joined['family_counts']==COUNTS and joined['solver_calls']==0
         and identity(joined['catalog'])==native.pin(inputs/'cases.jsonl.gz')
         and identity(joined['inputs_manifest'])==native.pin(inputs/'MANIFEST.json'),
         'Mathematical/native input boundary mismatch')
    need(len(joined['component_receipts'])==4, 'Incomplete exact input-binding components')
    marked_receipts = []
    for record in joined['component_receipts']:
        relative = relative_record(record,origin_binding)
        files.add(binding/relative,'math/binding/'+str(relative),record)
        component = read(binding/relative)
        if component.get('schema') == 'UNIFORM_K61_MARKED_UU_BINDING_1':
            need(component['status'] == 'PASS' and component['cases'] == 1358
                 and component['family_counts'] == {'D_UUU':679,'D_UUT':679}
                 and component['case_table'] == case_table,
                 'Marked component used a different case-index table')
            marked_receipts.append(component)
    need(len(marked_receipts) == 1, 'Exactly one marked input-binding component required')
    # Keep detailed execution records, not compiled objects or bulk emissions.
    for directory in (binding,binding/'checks'):
        for path in directory.iterdir():
            if path.suffix in ('.json','.log') and path.is_file():
                files.add(path,'math/binding/'+path.relative_to(binding).as_posix())
    return {'source_manifest':mp,'build_result':bp,'fresh_binding_result':rp,
            'modules':len(modules),'cases':CASES,'theorem_axioms':audit['axioms'],
            'binding_catalog_order_case_hashes_sha256':joined['catalog_order_case_hashes_sha256'],
            'live_build_custody_rechecked':live}


def package(path,files,release):
    """Write one fresh archive only after every native/mathematical gate passed."""
    need(release['schema']=='UNIFORM_K61_CURRENT_RELEASE_1' and release['cases']==CASES
         and release['native_runs']==RUNS and release['family_counts']==COUNTS
         and release['native']['status']=='PASS_NATIVE_CURRENT_56723'
         and release['mathematics']['cases']==CASES
         and release['mathematics']['live_build_custody_rechecked'] is True,
         'Native and fresh mathematical acceptance are required before packaging')
    need({'math/SOURCE_MANIFEST.json','math/build/BUILD_RESULT.json','math/binding/RUN_RESULT.json',
          'math/binding/FINAL_THEOREM_AUDIT.json','math/binding/checks/BINDING_RESULT.json'}<=set(files.entries),
         'Raw mathematical acceptance records missing')
    files.unchanged()
    with Path(path).open('xb') as output:
        with tarfile.open(fileobj=output,mode='w:gz',compresslevel=6) as archive:
            for member,(source,expected) in sorted(files.entries.items()):
                info = tarfile.TarInfo(member)
                info.size=expected['bytes']; info.mode=0o555 if member.rsplit('/',1)[-1] in native.SOLVERS else 0o644; info.mtime=0
                digest=hashlib.sha256(); size=0
                with source.open('rb') as stream:
                    class Checked:
                        def read(self,n=-1):
                            nonlocal size
                            block=stream.read(n);digest.update(block);size+=len(block);return block
                    archive.addfile(info,Checked())
                need({'bytes':size,'sha256':digest.hexdigest()}==expected,'File changed while packaging: '+member)
            # A release manifest is written last. A failed copy cannot leave
            # an apparently complete package manifest beside incomplete data.
            files.unchanged()
            raw=(json.dumps(release,sort_keys=True,indent=2)+'\n').encode()
            info=tarfile.TarInfo('RELEASE.json');info.size=len(raw);info.mode=0o644;info.mtime=0
            archive.addfile(info,io.BytesIO(raw))
    return native.pin(path)


def verify_package(root,formal):
    root,formal=Path(root),Path(formal)
    release_pin=native.pin(root/'RELEASE.json')
    release=read(root/'RELEASE.json')
    need(release['schema']=='UNIFORM_K61_CURRENT_RELEASE_1' and release['cases']==CASES
         and release['native_runs']==RUNS and release['family_counts']==COUNTS,
         'Wrong current release boundary')
    files=Files()
    files.add(root/'tools/uniform_release.py','tools/uniform_release.py',release['verifier'])
    files.add(root/'tools/uniform_verify.py','tools/uniform_verify.py',release['native_verifier'])
    report=inspect_native(root/'inputs',root/'sources/abd',root/'sources/c',root/'sources/balance',files,True)
    math=inspect_math(formal,root/'math/SOURCE_MANIFEST.json',root/'math/build',root/'math/binding',
                      root/'inputs',files)
    # Tool pins in raw binding records refer to the current checked repository;
    # additionally require the retained copies to match those exact bytes.
    for member,(source,expected) in list(files.entries.items()):
        if member.startswith(('math/tools/','current/tools/')):
            need(native.pin(root/member)==expected,'Retained binding tool changed')
            files.entries[member]=(root/member,expected)
    need(report==release['native'] and {k:v for k,v in math.items() if k!='live_build_custody_rechecked'}==
         {k:v for k,v in release['mathematics'].items() if k!='live_build_custody_rechecked'},
         'Release summary differs from preserved records')
    need(release['mathematics']['live_build_custody_rechecked'] is True,
         'Release was not gated on the live accepted build')
    actual={p.relative_to(root).as_posix() for p in root.rglob('*') if p.is_file() or p.is_symlink()}
    need(actual==set(files.entries)|{'RELEASE.json'},'Unexpected or missing release payload')
    files.unchanged()
    need(native.pin(root/'RELEASE.json')==release_pin, 'Release manifest changed during verification')
    return {'status':'PASS_CURRENT_RELEASE','cases':CASES,'native_runs':RUNS,'family_counts':COUNTS,
            'native':report,'mathematics':math,'new_solver_calls':0}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command',choices=('verify-native','package','verify-package'))
    parser.add_argument('--inputs',type=Path)
    parser.add_argument('--abd',type=Path)
    parser.add_argument('--c',type=Path)
    parser.add_argument('--balance',type=Path)
    parser.add_argument('--formal-root',type=Path,default=Path(__file__).resolve().parents[1]/'formal')
    parser.add_argument('--build',type=Path)
    parser.add_argument('--binding',type=Path)
    parser.add_argument('--root',type=Path)
    parser.add_argument('--archive',type=Path)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    if args.command=='verify-package':
        need(args.root is not None,'--root required')
        result=verify_package(args.root,args.formal_root)
    else:
        need(all(p is not None for p in (args.inputs,args.abd,args.c,args.balance)),
             '--inputs, --abd, --c, and --balance required')
        files=Files()
        result=inspect_native(args.inputs,args.abd,args.c,args.balance,files)
        if args.command=='package':
            files.add(Path(__file__),'tools/uniform_release.py')
            files.add(Path(native.__file__),'tools/uniform_verify.py')
            need(all(p is not None for p in (args.build,args.binding,args.archive)),
                 '--build, --binding, and fresh --archive required')
            math=inspect_math(args.formal_root,args.formal_root/'SOURCE_MANIFEST.json',args.build,
                              args.binding,args.inputs,files,True)
            need(result['catalog_order_case_hashes_sha256']==math['binding_catalog_order_case_hashes_sha256'],
                 'Native and exact-Lean joins used different ordered cases')
            release={'schema':'UNIFORM_K61_CURRENT_RELEASE_1','cases':CASES,'native_runs':RUNS,
                     'family_counts':COUNTS,'native':result,'mathematics':math,
                     'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
                     'verifier':native.pin(__file__),'native_verifier':native.pin(native.__file__),
                     'source_scope':'Only selected A/B/D, C and balanced case records are proof dependencies. Each source catalog and campaign metadata is preserved unchanged.',
                     'new_solver_calls':0}
            result={'status':'PACKAGED_CURRENT_RELEASE','archive':package(args.archive,files,release),
                    'cases':CASES,'native_runs':RUNS,'new_solver_calls':0}
        else:
            files.unchanged()
    text=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.output:
        with args.output.open('x') as stream:stream.write(text)
    print(text,end='')


if __name__=='__main__':
    main()
