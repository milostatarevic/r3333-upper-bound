#!/usr/bin/env python3
"""Portable custody and verification of native K60 Kissat evidence.

No Lean, SAT solver, archived Python tool, or generator is executed by verify.
Prepare calls only the hash-pinned current independent native auditors. Raw
records keep their original paths and commands; a declared origin maps them
into the archive. SQLite backup preserves records, not database page bytes.
"""
import argparse
import ast
from collections import Counter
from contextlib import ExitStack
from datetime import datetime, timezone
import gzip
import hashlib
import importlib.util
import io
import json
import math
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import sqlite3
import struct
import sys
import uuid

SCHEMA = 'K60_PORTABLE_NATIVE_EVIDENCE_2'
TOTAL = 296797
SOLVER_SHA = '05d6f3e9c402a1fe8853b0746e384e1b3d1c4a550e255f11daa2461d279aa848'
SOLVER_LICENSE_SHA = '0dbd8c6478aa03f62d720ed2256cf585cb93eba657201be1df217c4e920f162d'
SOLVER_LICENSE_BYTES = 1316
SOLVER_LICENSE_MEMBER = 'tools/KISSAT-LICENSE'
SPECS = {
 'e': (231168, 'inputs-e-exhaustive/manifest.json', '1c1fe1bbb2166d058b99a5e3ab16dfff0a81e0f802911879875ed055141cbedb', 'K60_E_NATIVE_CAMPAIGN_1'),
 'abd': (56374, 'inputs-abd-exhaustive/manifest.json', 'fc94af1694ca41df160da21950f48432668afa16014540ffbec79d96ecc6c50f', 'K60_ABD_NATIVE_CAMPAIGN_1'),
 'closure': (9255, 'inputs-direct-closure/manifest.json', '76670e2f9b4a43e4e6d6b1582a3137ab71ef095ed1b0c3bf55b131270d250cb3', 'K60_CLOSURE_NATIVE_CAMPAIGN_1'),
}
CHECKER_SHA = {
 'e': 'b245a77b5444dff3853382e4db777b3505d49d6501dba177ca6140ec75a25fb4',
 'abd': 'ee3662ffb38fd98e9f1d5b12c340429bf072ba69c51b8e8549d476d27b6829ea',
 'closure': 'df80c546c60ddf8b0936a8368994584810848b05a00f074ce06b6eb88d303c40',
}
E_FACTORS = [('UUU','D_UU',679,(0,1,2)), ('UUT','D_UU',679,(0,1,2,4,5,6,7,9,12)),
             ('UTT','D_UTT',6576,(0,1,2,4,5,6,7,9,12)), ('TTT','D_TTT',18204,(0,1,2,4,5,6,7,9,12))]
ABD_FACTORS = [('A','A',360,12),('B','B',5096,13),('D_UUU','D_UU',679,14),
 ('D_UUT','D_UU',679,14),('D_UTU','D_UTU',6576,14),('D_UTT','D_UTT',6576,14),
 ('D_TTU','D_TTU',18204,14),('D_TTT','D_TTT',18204,14)]
COMPONENTS = [
 ('entrances','inputs-k60-entrances/manifest.json','audit-k60-entrances.json',8532,'4ec3d6f6871d9638a908d1d70ada2d68e1e0095cebbd8627fc0a6d0e90b1abbf'),
 ('mixed_balance','balance-simplified-full/manifest.json','balance-simplified-full/audit-inputs.json',720,'0240d89463111e4fb51d8c13fb799d16524d8e10e826ed31962788440209db19'),
 ('all_five','inputs-balance-fiveguards-all/manifest.json','audit-balance-fiveguards-all.json',3,'5c39d4af5c9a65eafcfafad4db2473edc8a2529983304ab2bad9938302e3c803'),
]
CLOSURE_OWNERS = {'C1_ENTRANCE':692,'C2_ENTRANCE':7840,'BALANCE_BRACE_15':624,
                 'BALANCE_BRACE_16':96, **{'BALANCE_ALL_FIVE_'+x:1 for x in ('UU','UT','TT')}}
COLUMNS = ['case_id','attempt','owner','input_sha256','catalogue_sha256','solver_sha256',
 'limit_seconds','started_utc','finished_utc','elapsed_seconds','returncode','status',
 'command_json','log_sha256','log_gzip']
# Additional source controls where older audits record only a hash or no checker path.
EXTRA = [
 'check_inputs.py','check_k60_entrances.py','check_balance_inputs.py','check_balance_fiveguards_inputs.py',
 'check_e_campaign_inputs.py','check_e_cover_independent.py','check_abd_campaign_inputs.py','check_closure_campaign_inputs.py',
 'balance-simplified-full/check_catalogue.py','balance-simplified-full/certify_cover.py',
 'balance-simplified-full/projected-cover-rows.json','balance-analysis/anchors.py',
 'balance-simplification-pilot/check_pentagon_variant.py','balance-simplification-pilot/check_pilot.py',
 'balance-simplification-pilot/manifest-full.json','balance-simplification-pilot/audit-full.json',
 'inputs-balance-aligned-c1/manifest.json',
]
# Pinned import/data closure. PySAT is generation-only; portable verify never imports it.
EXTERNAL_IMPORTS = set(('argparse ast collections concurrent contextlib copy datetime fcntl functools '
 'gzip hashlib importlib io itertools json math os pathlib random re shutil signal sqlite3 '
 'statistics struct subprocess sys tarfile tempfile threading time traceback uuid pysat').split())
DATA_DEPENDENCIES = {
 'r3333-upper-bound/reproduce/uniform_balance.py': ['r3333-upper-bound/reproduce/data/balance_anchors.json'],
}
HASH_ALIASES = {
 'balance-simplified-full/manifest.json': {'recipe_sha256':'balance-simplified-full/generate_catalogue.py'},
 'balance-simplified-full/audit-inputs.json': {'auditor_sha256':'balance-simplified-full/check_catalogue.py'},
 'balance-simplified-full/projected-cover-audit.json': {'rows_sha256':'balance-simplified-full/projected-cover-rows.json'},
 'balance-simplification-pilot/audit-pentagon-only.json': {
   'auditor_sha256':'balance-simplification-pilot/check_pentagon_variant.py',
   'source_full_manifest_sha256':'balance-simplification-pilot/manifest-full.json',
   'source_full_independent_audit_sha256':'balance-simplification-pilot/audit-full.json'},
 'balance-simplification-pilot/audit-full.json': {'auditor_sha256':'balance-simplification-pilot/check_pilot.py'},
}
TRUST = ('Archived exact-input native Kissat outcomes and complete attempt/log histories. '
         'This is not an independently checked UNSAT-refutation certificate, a Lean proof, '
         'or the separate formal/input-binding release gate.')


def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def file_pin(path):
    h = hashlib.sha256(); size = 0
    with Path(path).open('rb') as f:
        for b in iter(lambda: f.read(1 << 20), b''):
            h.update(b); size += len(b)
    return {'sha256':h.hexdigest(), 'bytes':size}


def read_json(path):
    def pairs(values):
        result = {}
        for k,v in values:
            require(k not in result, 'Duplicate JSON key: '+k); result[k] = v
        return result
    return json.loads(Path(path).read_bytes(), object_pairs_hook=pairs,
                      parse_constant=lambda x: (_ for _ in ()).throw(ValueError('Nonfinite JSON: '+x)))


def safe_member(value):
    require(isinstance(value,str) and value and '\\' not in value and '\x00' not in value,
            'Invalid archive member')
    p = PurePosixPath(value)
    require(not p.is_absolute() and str(p)==value and all(x not in ('','.','..') and ':' not in x for x in p.parts),
            'Unsafe archive member: '+value)
    return p


def absolute_origin(value):
    require(isinstance(value,str) and '\\' not in value and '\x00' not in value, 'Invalid original path')
    p = PurePosixPath(value)
    require(p.is_absolute() and str(p)==value and '..' not in p.parts, 'Noncanonical original path')
    return p


def normalize_join(parent, relative):
    """Normalize recorded relative paths; archive member names never use this."""
    require(isinstance(relative,str) and '\\' not in relative and '\x00' not in relative, 'Bad recorded path')
    p = PurePosixPath(relative)
    if p.is_absolute():
        return str(absolute_origin(relative))
    parts = list(absolute_origin(str(parent)).parts)
    for part in p.parts:
        if part == '..':
            require(len(parts)>1, 'Recorded path escapes filesystem root'); parts.pop()
        elif part != '.':
            parts.append(part)
    return str(PurePosixPath(*parts))


def checked_solver_identity(command, identity):
    """Exactly one captured executable target, never a general outside-path allowlist."""
    absolute_origin(command)
    require(isinstance(identity,dict) and set(identity)=={'path','sha256','bytes'},
            'Malformed captured solver identity')
    absolute_origin(identity['path'])
    require(identity['sha256']==SOLVER_SHA and type(identity['bytes']) is int and identity['bytes']>0,
            'Unbound captured solver identity')
    return dict(identity)


def check_solver_identity(origins, audit_pin):
    identity=checked_solver_identity(origins['solver'],origins['solver_identity'])
    require(audit_pin==identity, 'Native audit solver identity differs from the captured executable')


def solver_license_record(identity):
    """The exact installed notice accompanying the captured executable prefix."""
    return {'path': str(absolute_origin(identity['path']).parent.parent/'LICENSE'),
            'member': SOLVER_LICENSE_MEMBER, 'sha256': SOLVER_LICENSE_SHA,
            'bytes': SOLVER_LICENSE_BYTES}


def check_solver_license(store, record):
    require(store.solver_identity is not None, 'License requires a captured solver identity')
    expected=solver_license_record(store.solver_identity)
    require(record==expected, 'Missing or changed Kissat license provenance')
    require(file_pin(store.get(expected['path']))=={k:expected[k] for k in ('sha256','bytes')},
            'Changed Kissat license notice')


class Paths:
    def __init__(self, workspace, solver, solver_identity=None):
        self.workspace = absolute_origin(workspace)
        self.solver = str(absolute_origin(solver))
        self.solver_identity = (checked_solver_identity(self.solver,solver_identity)
                                if solver_identity is not None else None)
        self.solver_paths = {self.solver}
        if self.solver_identity is not None:
            self.solver_paths.add(self.solver_identity['path'])
        self.solver_license = (solver_license_record(self.solver_identity)['path']
                               if self.solver_identity is not None else None)
        self.pilot = self.workspace/'k60-pilot'

    def member(self, origin):
        p = absolute_origin(str(origin))
        if str(p) in self.solver_paths:
            return 'tools/kissat'
        if str(p)==self.solver_license:
            return SOLVER_LICENSE_MEMBER
        try:
            rel = p.relative_to(self.workspace)
        except ValueError as e:
            raise ValueError('Original path outside declared roots: '+str(p)) from e
        require(str(rel)!='.', 'A file, not the origin directory, is required')
        return str(safe_member('workspace/'+str(rel)))

    def candidates(self, document, recorded):
        if PurePosixPath(recorded).is_absolute():
            return [str(absolute_origin(recorded))]
        bases = [PurePosixPath(document).parent,self.pilot,self.workspace/'r3333-upper-bound',self.workspace]
        if PurePosixPath(document).parent==self.pilot:
            for family,(_,relative,*_) in SPECS.items():
                if PurePosixPath(document).name=='audit-'+family+'-campaign-inputs.json':
                    bases.insert(1,self.pilot/PurePosixPath(relative).parent)
        if PurePosixPath(document).parent==self.pilot/'inputs-balance-fiveguards-all':
            bases.insert(1,self.pilot/'inputs-balance-aligned-c1')
        result = []
        for base in bases:
            path = normalize_join(base,recorded)
            try:
                self.member(path)  # Never search outside the declared roots.
            except ValueError:
                continue
            if path not in result:
                result.append(path)
        require(result, 'Recorded dependency leaves declared roots')
        return result

    def checked_origin(self, document, record, path_key='path', hash_key='sha256', bytes_key='bytes'):
        require(hash_key in record and re.fullmatch('[0-9a-f]{64}',record[hash_key]), 'Malformed dependency hash')
        for origin in self.candidates(document,record[path_key]):
            path = self.available(origin)
            if path is not None:
                pin = file_pin(path)
                if pin['sha256']==record[hash_key] and (bytes_key not in record or pin['bytes']==record[bytes_key]):
                    self.get(origin)
                    return origin
        raise ValueError('Missing or changed dependency: '+str(record[path_key])+' from '+str(document))

    def checked(self, document, record, path_key='path', hash_key='sha256', bytes_key='bytes'):
        return self.get(self.checked_origin(document,record,path_key,hash_key,bytes_key))

    def json(self, origin):
        return read_json(self.get(str(origin)))


class Archive(Paths):
    def __init__(self, root, manifest, manifest_sha256):
        require(Path(root).resolve()==Path(root).absolute() and not Path(root).is_symlink(), 'Linked archive root')
        self.root = Path(root).resolve()
        mp = self.root/'NATIVE_RELEASE.json'
        require(file_pin(mp)['sha256']==manifest_sha256, 'Archive manifest hash mismatch')
        self.manifest = manifest
        super().__init__(manifest['origins']['workspace'],manifest['origins']['solver'],
                         manifest['origins'].get('solver_identity'))
        self.files = manifest['files']
        require(isinstance(self.files,dict), 'Malformed file manifest')
        for member,pin in self.files.items():
            p = self.path(member)
            require(set(pin)=={'sha256','bytes'} and type(pin['bytes']) is int and pin['bytes']>=0,
                    'Malformed file pin')
            require(file_pin(p)==pin, 'Archived file changed: '+member)
        actual = set()
        for p in self.root.rglob('*'):
            require(not p.is_symlink(), 'Archive symlink forbidden: '+str(p))
            if p.is_file(): actual.add(p.relative_to(self.root).as_posix())
            else: require(p.is_dir(), 'Nonregular archive entry')
        require(actual==set(self.files)|{'NATIVE_RELEASE.json'}, 'Missing or unexpected archive files')

    def path(self, member):
        rel = safe_member(member); p = self.root
        for part in rel.parts:
            p /= part
            require(not p.is_symlink(), 'Archive symlink forbidden')
        require(p.is_file(), 'Missing regular archive file: '+member)
        return p

    def available(self, origin):
        member = self.member(origin)
        return self.path(member) if member in self.files else None

    def get(self, origin):
        member = self.member(origin)
        require(member in self.files, 'Unpinned archived dependency: '+member)
        return self.path(member)


class Collector(Paths):
    def __init__(self, workspace, solver, root, solver_identity=None):
        super().__init__(str(workspace),solver,solver_identity)
        self.root = Path(root); self.files = {}; self.watched = {}

    def available(self, origin):
        p = Path(origin)
        self.member(origin)
        if str(origin)==self.solver and self.solver_identity is not None:
            require(str(p.resolve(strict=True))==self.solver_identity['path'],
                    'Original solver command resolves to a different executable')
        if str(origin)!=self.solver:
            require(p.resolve()==p, 'Linked source path forbidden: '+str(p))
        return p if p.is_file() else None

    def get(self, origin):
        member = self.member(origin)
        if str(origin)==self.solver_license:
            source=self.available(origin)
            require(source is not None, 'Missing captured Kissat license notice')
            require(file_pin(source)=={'sha256':SOLVER_LICENSE_SHA,'bytes':SOLVER_LICENSE_BYTES},
                    'Changed Kissat license notice')
        if str(origin) in self.solver_paths and self.solver_identity is not None:
            source=self.available(origin)
            require(source is not None, 'Missing captured solver executable')
            expected={k:self.solver_identity[k] for k in ('sha256','bytes')}
            require(file_pin(source)==expected, 'Captured solver executable changed')
            self.watched[str(origin)]=expected
            if member in self.files:
                require(self.files[member]==expected, 'Solver alias maps to different retained bytes')
        if member not in self.files:
            source = self.available(origin)
            require(source is not None and source.is_file() and (str(origin)==self.solver or not source.is_symlink()), 'Invalid source file')
            before = file_pin(source)
            target = self.root/member; target.parent.mkdir(parents=True,exist_ok=True)
            with source.open('rb') as inp, target.open('xb') as out:
                shutil.copyfileobj(inp,out,1 << 20)
            require(file_pin(target)==before==file_pin(source), 'Source changed while copying')
            self.files[member] = before; self.watched[str(origin)] = before
        return self.root/member

    def add_bytes(self, member, data):
        safe_member(member); require(member not in self.files, 'Duplicate generated member')
        p=self.root/member; p.parent.mkdir(parents=True,exist_ok=True); p.write_bytes(data)
        self.files[member]=file_pin(p)
        return p

    def unchanged(self):
        if self.solver_identity is not None:
            self.available(self.solver)  # Also reject a retargeted link with identical bytes.
        for origin,pin in self.watched.items():
            require(file_pin(origin)==pin,'Original evidence changed: '+origin)


def complete_audit(a, count):
    require(a.get('passed') is True and a.get('completion_claim') is True and not a.get('requires_attention'),
            'Incomplete or attention-required independent native audit')
    require(a['total_cases']==a['unique_accepted_unsat_cases']==count and a['remaining_cases']==0,
            'Incomplete distinct-case UNSAT coverage')
    require(a['attempts_seen']==a['attempts_integrity_checked'] and not a['invalid_attempts_or_histories']
            and not a['sat_case_ids'] and not a['sat_unsat_conflict_ids']
            and not a['attempt_status_counts'].get('ERROR'), 'Invalid or conflicting independent native history')


def dependency_records(value):
    if isinstance(value,dict):
        for p,h,b in [('path','sha256','bytes'),('raw_path','raw_sha256','raw_bytes'),
                      ('cnf','sha256','bytes'),('metadata','metadata_sha256','metadata_bytes'),
                      ('source_cnf','source_sha256','source_bytes')]:
            if isinstance(value.get(p),str) and h in value:
                yield value,p,h,b
        for key,digest in value.items():
            stem=key[:-7] if key.endswith('_sha256') else ''
            path=value.get(stem)
            if stem and isinstance(path,str) and (path.startswith('/') or '/' in path or Path(path).suffix in ('.json','.py','.cnf','.gz')):
                yield {'path':path,'sha256':digest},'path','sha256','bytes'
        for child in value.values(): yield from dependency_records(child)
    elif isinstance(value,list):
        for child in value: yield from dependency_records(child)


def control_json(origin):
    p=PurePosixPath(origin)
    return p.suffix=='.json' and ('source-raw' not in p.parts) and (
        'manifest' in p.name.lower() or 'audit' in p.name.lower() or 'cover' in p.name.lower()
        or p.name.endswith('.metadata.json') or 'anchor-library' in p.name)


def dependencies(store, roots):
    """Traverse pinned control records; dense source rows are opaque authenticated data.

    Old source rows may name historical CNFs; those are not adopted proof inputs.
    Local Python imports are retained as source only and are never executed here.
    """
    queue=list(map(str,roots)); seen=set()
    while queue:
        origin=queue.pop()
        if origin in seen: continue
        seen.add(origin); p=store.get(origin)
        if control_json(origin):
            doc=read_json(p)
            for record,pk,hk,bk in dependency_records(doc):
                child=store.checked_origin(origin,record,pk,hk,bk)
                if control_json(child) or child.endswith('.py'): queue.append(child)
            try: rel=str(PurePosixPath(origin).relative_to(store.pilot))
            except ValueError: rel=''
            for key,target in HASH_ALIASES.get(rel,{}).items():
                require(key in doc,'Missing audit dependency hash')
                child=str(store.pilot/target)
                store.checked(origin,{'path':child,'sha256':doc[key]}); queue.append(child)
        elif origin.endswith('.py'):
            tree=ast.parse(p.read_text())
            names=[]
            for node in ast.walk(tree):
                if isinstance(node,ast.Import): names.extend(x.name.split('.')[0] for x in node.names)
                if isinstance(node,ast.ImportFrom) and node.module: names.append(node.module.split('.')[0])
            for name in names:
                found=False
                for base in [PurePosixPath(origin).parent,store.pilot,store.pilot/'balance-analysis',store.workspace/'r3333-upper-bound/reproduce']:
                    child=str(base/(name+'.py'))
                    if store.available(child) is not None:
                        queue.append(child); found=True; break
                require(found or name in EXTERNAL_IMPORTS,'Unretained Python source dependency: '+name+' from '+origin)
            relative=str(PurePosixPath(origin).relative_to(store.workspace))
            for child in DATA_DEPENDENCIES.get(relative,[]):
                queue.append(str(store.workspace/child))
    return seen


def catalogue(store, family, campaign):
    count,rel,expected_hash,_=SPECS[family]
    origin=str(store.pilot/rel)
    require(campaign['catalogue']==origin and campaign['catalogue_sha256']==expected_hash,'Wrong frozen catalogue')
    p=store.get(origin); require(file_pin(p)['sha256']==expected_hash,'Frozen catalogue changed')
    m=read_json(p); a=store.json(campaign['audit'])
    require(file_pin(store.get(campaign['audit']))['sha256']==campaign['audit_sha256'],'Input audit changed')
    require(a.get('passed') is True and a['catalogue_sha256']==expected_hash
            and a['cases_checked']==a['full_cnf_hashes_checked']==count,'Incomplete exact-input audit')
    dependencies(store,[origin,campaign['audit']])
    expected={}; ordered=hashlib.sha256(); census=Counter()
    def add(cid,owner,digest,units=None):
        require(cid not in expected and re.fullmatch('[0-9a-f]{64}',digest),'Duplicate/invalid case identity')
        expected[cid]={'owner':owner,'sha256':digest,'units':units}
        ordered.update(f'{cid} {digest}\n'.encode()); census[owner]+=1
    if family in ('e','abd'):
        require(m['schema']==('K60_E_FACTORIZED_1' if family=='e' else 'K60_ABD_FACTORIZED_1'),'Catalogue schema')
        ledger=store.checked(origin,m['hash_index']).read_bytes()
        require(len(ledger)==34*count and m['hash_index']['record_bytes']==34
                and sha(ledger)==a['hash_index']['sha256'],'Hash ledger disagreement')
        factors=E_FACTORS if family=='e' else ABD_FACTORS
        require(len(m['factors'])==len(factors),'Wrong factor count'); ordinal=0; units_census=Counter()
        for f,(owner,key,n,last) in zip(m['factors'],factors):
            reps=last if family=='e' else (None,)
            require((f['owner'],f['source_key'],f['source_count'],f['ordinal_start'],f['case_count'])==
                    (owner,key,n,ordinal,n*len(reps)),'Wrong factor product')
            require(tuple(f['deleted_reference_representatives'])==last if family=='e' else f['deleted_old_vertex']==last,
                    'Wrong deletion representatives')
            local=Counter()
            for index in range(n):
                for deleted in reps:
                    off=34*ordinal; digest=ledger[off:off+32].hex(); units=struct.unpack_from('<H',ledger,off+32)[0]
                    require(units in (503,507,517) if family=='e' else 500<=units<=600,'Wrong unit count')
                    cid=f'E_{owner}_s{index:05d}_d{deleted:02d}' if family=='e' else f'{owner}_s{index:05d}'
                    add(cid,owner,digest,units); ordinal+=1; local[units]+=1; units_census[units]+=1
            require(f['ordinal_stop']==ordinal,'Wrong factor end')
            if family=='abd': require(f['unit_count_histogram']=={str(k):v for k,v in local.items()},'Unit histogram')
        if family=='e': require(dict(units_census)=={503:65988,507:151344,517:13836},'E unit census')
    else:
        require(m['schema']=='K60_DIRECT_CLOSURE_CATALOGUE_1' and len(m['components'])==3,'Closure schema')
        for comp,(name,relpath,audit,n,digest) in zip(m['components'],COMPONENTS):
            require(comp=={'name':name,'manifest':relpath,'input_audit':audit,'case_count':n},'Wrong closure component')
            sp=store.get(str(store.pilot/relpath)); require(file_pin(sp)['sha256']==digest,'Changed component')
            source=read_json(sp); require(len(source['cases'])==n,'Component census')
            for row in source['cases']:
                owner=row['family'] if name=='entrances' else 'BALANCE_BRACE_'+str(row['brace_size']) if name=='mixed_balance' else 'BALANCE_ALL_FIVE_'+row['owner']
                add(row['id'],owner,row['sha256'])
        require(dict(census)==CLOSURE_OWNERS,'Wrong closure owner census')
    require(len(expected)==count and ordered.hexdigest()==m['ordered_case_hash_sha256']==a['ordered_case_hash_sha256'],
            'Incomplete ordered exact-input boundary')
    return expected


def native_log(blob, expected_hash):
    require(type(blob) is bytes,'Native log must be a BLOB')
    digest=hashlib.sha256(); total=0; carry=b''; overlong=False; verdicts=set()
    with gzip.GzipFile(fileobj=io.BytesIO(blob),mode='rb') as stream:
        for block in iter(lambda: stream.read(1 << 20),b''):
            digest.update(block); total+=len(block)
            pieces=block.split(b'\n')
            for i,piece in enumerate(pieces):
                ended=i<len(pieces)-1
                if not overlong:
                    carry+=piece
                    if len(carry)>64: carry=b''; overlong=True
                if ended:
                    if not overlong:
                        line=carry.rstrip(b'\r')
                        if line in (b's SATISFIABLE',b's UNSATISFIABLE'): verdicts.add(line)
                    carry=b''; overlong=False
        if not overlong and carry in (b's SATISFIABLE',b's UNSATISFIABLE'): verdicts.add(carry)
    require(digest.hexdigest()==expected_hash,'Native log hash mismatch')
    require(len(verdicts)<=1,'Contradictory native verdict lines')
    return verdicts,total


def check_attempt(row, expected, campaign, origin_directory):
    require(set(row)==set(COLUMNS),'Unexpected attempt columns')
    cid=row['case_id']; require(cid in expected,'Unknown case ID')
    require(type(row['attempt']) is int and row['attempt']>=1,'Invalid attempt number')
    require(row['owner']==expected[cid]['owner'] and row['input_sha256']==expected[cid]['sha256'],'Wrong exact input hash or owner')
    require(row['catalogue_sha256']==campaign['catalogue_sha256'] and row['solver_sha256']==campaign['solver_sha256'],'Wrong catalogue/solver pin')
    cap=row['limit_seconds']; require(type(cap) is int and cap in campaign['limits_seconds'],'Wrong time limit')
    elapsed=row['elapsed_seconds']; require(type(elapsed) in (int,float) and math.isfinite(elapsed) and elapsed>=0,'Invalid elapsed time')
    start=datetime.fromisoformat(row['started_utc']); end=datetime.fromisoformat(row['finished_utc'])
    require(start.tzinfo is not None and end.tzinfo is not None and end>=start,'Invalid timestamps')
    origin=absolute_origin(origin_directory)
    command=[campaign['solver'],f'--time={cap}',str(origin/'active-inputs'/f'{cid}.a{row["attempt"]}.cnf')]
    require(json.loads(row['command_json'])==command,'Changed original native command')
    verdicts,total=native_log(row['log_gzip'],row['log_sha256'])
    status=row['status']; require(status in ('UNSAT','SAT','TIMEOUT','INTERRUPTED','ERROR'),'Unknown status')
    if status=='UNSAT': require(row['returncode']==20 and verdicts=={b's UNSATISFIABLE'},'Invalid UNSAT verdict/exit')
    elif status=='SAT': require(row['returncode']==10 and verdicts=={b's SATISFIABLE'},'Invalid SAT verdict/exit')
    else: require(not verdicts and row['returncode'] not in (10,20),'Unresolved status contradicts native result')
    return status,total


def audit_history(database, expected, campaign, origin_directory):
    db=sqlite3.connect(Path(database).resolve().as_uri()+'?mode=ro&immutable=1',uri=True)
    db.row_factory=sqlite3.Row
    try:
        db.execute('PRAGMA query_only=ON'); db.execute('PRAGMA trusted_schema=OFF')
        objects=list(db.execute("SELECT name,type FROM sqlite_master WHERE name NOT LIKE 'sqlite_%'"))
        require({r['name'] for r in objects if r['type']=='table'}=={'attempts','metadata'} and
                all(r['type'] in ('table','index') for r in objects),'Unexpected SQLite schema objects')
        require([r['name'] for r in db.execute('PRAGMA table_info(attempts)')]==COLUMNS,'Wrong attempt schema')
        require(db.execute('PRAGMA quick_check').fetchone()[0]=='ok','Corrupt SQLite snapshot')
        h=hashlib.sha256(); counts=Counter(); histories={}; unsat=set(); logs=0; rows=0
        for raw in db.execute('SELECT * FROM attempts ORDER BY case_id,attempt'):
            row=dict(raw); status,size=check_attempt(row,expected,campaign,origin_directory)
            require(status not in ('SAT','ERROR'),'SAT or ERROR evidence forbids release')
            number=histories.get(row['case_id'],0)+1
            require(row['attempt']==number,'Noncontiguous or duplicate attempt history')
            histories[row['case_id']]=number
            if status=='UNSAT': unsat.add(row['case_id'])
            bound={k:v for k,v in row.items() if k!='log_gzip'}
            bound['compressed_log_sha256']=sha(row['log_gzip'])
            h.update((json.dumps(bound,sort_keys=True,separators=(',',':'))+'\n').encode())
            counts[status]+=1; rows+=1; logs+=size
        require(unsat==set(expected),'Incomplete native UNSAT case coverage')
        # Retain and validate the second raw table as part of the archive snapshot.
        metadata=list(db.execute('SELECT key,value FROM metadata ORDER BY key'))
        require(len({r['key'] for r in metadata})==len(metadata),'Duplicate metadata keys')
        return {'cases':len(expected),'attempts':rows,'attempt_status_counts':dict(counts),
                'ordered_row_and_compressed_log_hash_sha256':h.hexdigest(),'native_log_bytes':logs}
    finally:
        db.close()


def verify(root, manifest_sha256):
    require(re.fullmatch('[0-9a-f]{64}',manifest_sha256), 'Malformed manifest pin')
    require(file_pin(Path(root)/'NATIVE_RELEASE.json')['sha256']==manifest_sha256, 'Archive manifest hash mismatch')
    manifest=read_json(Path(root)/'NATIVE_RELEASE.json')
    require(manifest.get('schema')==SCHEMA and manifest.get('native_only') is True,'Wrong native archive schema')
    require(manifest.get('trust')==TRUST,'Altered native evidence trust statement')
    require(manifest['family_counts']=={k:v[0] for k,v in SPECS.items()} and manifest['total_cases']==TOTAL,'Wrong release census')
    require(set(manifest['campaigns'])==set(SPECS),'Incomplete campaign set')
    require(set(manifest['origins'])=={'workspace','solver','solver_identity'},
            'Native capsule must declare the command and authenticated executable identity')
    identity=checked_solver_identity(manifest['origins']['solver'],manifest['origins']['solver_identity'])
    store=Archive(root,manifest,manifest_sha256)
    require(file_pin(store.path('tools/native_evidence.py'))==file_pin(__file__),'Verifier source differs from archive pin')
    require(file_pin(store.get(store.solver))=={k:identity[k] for k in ('sha256','bytes')},
            'Wrong original Kissat binary')
    check_solver_license(store,manifest.get('solver_license'))
    roots=[str(store.pilot/x) for x in EXTRA]; results={}
    for family,(count,_,_,schema) in SPECS.items():
        spec=manifest['campaigns'][family]; origin=str(store.pilot/('campaign-'+family+'-kissat'))
        require(spec['origin_directory']==origin and spec['campaign']==store.member(origin+'/campaign.json')
                and spec['database']==store.member(origin+'/results.sqlite3'),'Changed campaign origin mapping')
        c=store.json(origin+'/campaign.json')
        require(c['schema']==schema and c['case_count']==count and c['solver']==store.solver
                and c['solver_sha256']==SOLVER_SHA and c['solver_version']=='4.0.4','Wrong native campaign identity')
        require(type(c['jobs']) is int and 1<=c['jobs']<=12 and c['limits_seconds']==sorted(set(c['limits_seconds']))
                and all(type(x) is int and x>0 for x in c['limits_seconds']),'Invalid native execution policy')
        runner=str(store.pilot/f'run_{family}_campaign.py'); checker=str(store.pilot/f'check_{family}_campaign_results.py')
        require(file_pin(store.get(runner))['sha256']==c['runner_sha256'],'Changed pinned runner')
        require(file_pin(store.get(checker))['sha256']==CHECKER_SHA[family],'Changed independent native auditor')
        a=read_json(store.path(spec['independent_audit'])); complete_audit(a,count)
        check_solver_identity(manifest['origins'],a['pins']['solver'])
        require(a['campaign']['path']==origin+'/campaign.json' and a['campaign']['sha256']==file_pin(store.get(origin+'/campaign.json'))['sha256'],
                'Independent audit uses a different campaign')
        require(a['checker']['path']==checker and a['checker']['sha256']==CHECKER_SHA[family], 'Unbound independent native auditor')
        expected=catalogue(store,family,c)
        result=audit_history(store.get(origin+'/results.sqlite3'),expected,c,origin)
        require(result['attempts']==a['attempts_seen']==a['database_snapshot']['rows'] and
                result['attempt_status_counts']==a['attempt_status_counts'] and
                result['ordered_row_and_compressed_log_hash_sha256']==a['database_snapshot']['ordered_row_and_compressed_log_hash_sha256'] and
                result['native_log_bytes']==a['native_log_bytes_checked'],'Snapshot differs from independently audited complete history')
        require(a['pins']['manifest']['sha256']==c['catalogue_sha256'] and a['pins']['input_audit']['sha256']==c['audit_sha256']
                and a['pins']['solver']['sha256']==SOLVER_SHA,'Independent audit pin disagreement')
        if family!='e':
            previous='e' if family=='abd' else 'abd'; previous_count=SPECS[previous][0]
            prerequisite=origin+'/prerequisite-'+previous+'-audit.json'; prior=store.json(prerequisite)
            require(file_pin(store.get(prerequisite))['sha256']==c['prerequisite_'+previous]['audit_sha256'] and
                    c['prerequisite_'+previous]['accepted_unsat_cases']==previous_count,'Changed campaign prerequisite')
            complete_audit(prior,previous_count)
            check_solver_identity(manifest['origins'],prior['pins']['solver'])
            roots.append(prerequisite)
        roots.extend([runner,checker,c['audit'],c['catalogue']]); results[family]=result
    dependencies(store,roots)
    require(manifest['verification']==results,'Archive summary differs from raw evidence')
    return {'schema':'K60_PORTABLE_NATIVE_VERIFICATION_2','passed':True,'total_cases':TOTAL,
            'campaigns':results,'manifest_sha256':manifest_sha256,'solver_executed':False,'trust':TRUST}


def snapshot_database(source, destination):
    """SQLite's read-only backup includes committed WAL content without source writes."""
    src=sqlite3.connect(Path(source).resolve().as_uri()+'?mode=ro',uri=True)
    dst=sqlite3.connect(destination)
    try:
        src.execute('PRAGMA query_only=ON'); src.backup(dst)
    finally:
        dst.close(); src.close()


def prepare(workspace, output):
    verifier_pin=file_pin(__file__)
    workspace=Path(workspace).resolve(); pilot=workspace/'k60-pilot'; output=Path(output).absolute()
    require(output.resolve()==output,'Linked output parent forbidden')
    require(not output.exists(),'Output must be fresh')
    # Fast fail-closed preflight. Passed flags NEVER replace the fresh audits below.
    for family,(count,*_) in SPECS.items():
        p=pilot/f'audit-{family}-campaign-results.json'
        require(p.is_file(),'Missing completed independent audit: '+family)
        complete_audit(read_json(p),count)
    import fcntl
    sys.dont_write_bytecode=True
    with ExitStack() as locks:
        reports={}; campaigns={}
        for family,(count,*_) in SPECS.items():
            directory=pilot/('campaign-'+family+'-kissat')
            lock=locks.enter_context((directory/'controller.lock').open('rb'))
            fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
            checker=pilot/f'check_{family}_campaign_results.py'
            require(file_pin(checker)['sha256']==CHECKER_SHA[family],'Independent native auditor changed')
            spec=importlib.util.spec_from_file_location('_k60_local_audit_'+family,checker)
            module=importlib.util.module_from_spec(spec); spec.loader.exec_module(module)
            reports[family]=module.audit_campaign(directory,1000)
            complete_audit(reports[family],count)
            require(file_pin(checker)['sha256']==CHECKER_SHA[family],'Auditor changed during execution')
            campaigns[family]=read_json(directory/'campaign.json')
        require({c['solver'] for c in campaigns.values()}=={campaigns['e']['solver']} and
                {c['solver_sha256'] for c in campaigns.values()}=={SOLVER_SHA},'Campaign solver disagreement')
        identity=checked_solver_identity(campaigns['e']['solver'],reports['e']['pins']['solver'])
        origins={'workspace':str(workspace),'solver':campaigns['e']['solver'],'solver_identity':identity}
        for report in reports.values():
            check_solver_identity(origins,report['pins']['solver'])
        command_path=Path(origins['solver'])
        require(str(command_path.resolve(strict=True))==identity['path'] and
                file_pin(command_path)=={k:identity[k] for k in ('sha256','bytes')},
                'Captured solver command/identity disagreement')
        stage=output.with_name(output.name+'.partial-'+uuid.uuid4().hex[:12]); stage.mkdir(parents=True)
        store=Collector(workspace,campaigns['e']['solver'],stage,identity)
        try:
            roots=[str(pilot/x) for x in EXTRA]; result={}; entries={}
            store.get(store.solver)
            store.get(identity['path'])
            license_record=solver_license_record(identity)
            check_solver_license(store,license_record)
            for family,c in campaigns.items():
                origin=str(pilot/('campaign-'+family+'-kissat')); store.get(origin+'/campaign.json')
                expected=catalogue(store,family,c)
                for name in [f'run_{family}_campaign.py',f'check_{family}_campaign_results.py']:
                    roots.append(str(pilot/name))
                if family!='e': roots.append(origin+'/prerequisite-'+('e' if family=='abd' else 'abd')+'-audit.json')
                member=store.member(origin+'/results.sqlite3'); target=stage/member; target.parent.mkdir(parents=True,exist_ok=True)
                snapshot_database(origin+'/results.sqlite3',target); store.files[member]=file_pin(target)
                result[family]=audit_history(target,expected,c,origin)
                require(result[family]['ordered_row_and_compressed_log_hash_sha256']==reports[family]['database_snapshot']['ordered_row_and_compressed_log_hash_sha256'],
                        'SQLite changed after independent audit')
                audit_member='audits/'+family+'-native.json'
                store.add_bytes(audit_member,(json.dumps(reports[family],indent=2)+'\n').encode())
                entries[family]={'origin_directory':origin,'campaign':store.member(origin+'/campaign.json'),
                                 'database':member,'independent_audit':audit_member,'snapshot_method':'SQLite read-only backup; raw rows and compressed log BLOBs unchanged'}
            dependencies(store,roots)
            require(file_pin(__file__)==verifier_pin, 'Verifier changed during preparation')
            store.add_bytes('tools/native_evidence.py',Path(__file__).read_bytes())
            store.unchanged()
            manifest={'schema':SCHEMA,'native_only':True,'origins':origins,
                      'solver_license':license_record,
                      'family_counts':{k:v[0] for k,v in SPECS.items()},'total_cases':TOTAL,
                      'files':dict(sorted(store.files.items())),'campaigns':entries,'verification':result,
                      'created_utc':datetime.now(timezone.utc).isoformat(),'trust':TRUST}
            mp=stage/'NATIVE_RELEASE.json'; mp.write_text(json.dumps(manifest,sort_keys=True,indent=2)+'\n')
            digest=file_pin(mp)['sha256']; verify(stage,digest); store.unchanged()
            require(file_pin(__file__)==verifier_pin, 'Verifier changed during verification')
            require(not output.exists(),'Output appeared during preparation'); stage.rename(output)
            return {'passed':True,'root':str(output),'manifest_sha256':digest,'total_cases':TOTAL,'trust':TRUST}
        except Exception as e:
            mp=stage/'NATIVE_RELEASE.json'
            if mp.exists(): mp.rename(stage/'REJECTED_MANIFEST.json')
            (stage/'FAILED.json').write_text(json.dumps({'passed':False,'error':str(e)},indent=2)+'\n')
            raise


def main():
    ap=argparse.ArgumentParser(description=__doc__); sub=ap.add_subparsers(dest='command',required=True)
    p=sub.add_parser('prepare'); p.add_argument('--workspace',type=Path,required=True); p.add_argument('--output',type=Path,required=True)
    p=sub.add_parser('verify'); p.add_argument('--root',type=Path,required=True); p.add_argument('--manifest-sha256',required=True)
    args=ap.parse_args()
    try:
        result=prepare(args.workspace,args.output) if args.command=='prepare' else verify(args.root,args.manifest_sha256)
        print(json.dumps(result,indent=2)); return 0
    except Exception as e:
        print(json.dumps({'passed':False,'error':str(e)},indent=2),file=sys.stderr); return 2

if __name__=='__main__':
    sys.exit(main())
