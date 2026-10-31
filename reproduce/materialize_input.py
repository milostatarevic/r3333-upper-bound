#!/usr/bin/env python3
"""Export one frozen K60 DIMACS input using the retained pinned catalogue code.

This actively imports generator code; it is separate from passive evidence
verification. No solver, Lean, Git, campaign runner or subprocess is invoked.
"""
import argparse
from contextlib import contextmanager
import hashlib
import json
import os
from pathlib import Path
import sys
import types

CATALOGUES = {
    'e': ('inputs-e-exhaustive/manifest.json',
          '1c1fe1bbb2166d058b99a5e3ab16dfff0a81e0f802911879875ed055141cbedb'),
    'abd': ('inputs-abd-exhaustive/manifest.json',
            'fc94af1694ca41df160da21950f48432668afa16014540ffbec79d96ecc6c50f'),
    'closure': ('inputs-direct-closure/manifest.json',
                '76670e2f9b4a43e4e6d6b1582a3137ab71ef095ed1b0c3bf55b131270d250cb3'),
}
# Transitive imports not listed separately in the E/ABD recipe records.
HELPERS = {
    'uniform_c': ('r3333-upper-bound/reproduce/uniform_c.py',
        '6f8f404a520bb696b7be03f8fc4de9d4ce582df8812fd94739bc319aa91b4a4c'),
    'uniform_balance': ('r3333-upper-bound/reproduce/uniform_balance.py',
        'a419fdba5a0bf6bf281d973cb6c38dd62c5d0524ac6a5c856b9c4e7f387d493a'),
}


def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def source_path(workspace, path):
    path=Path(path).resolve()
    try:
        path.relative_to(workspace)
    except ValueError as e:
        raise ValueError('Pinned source leaves the explicit workspace') from e
    require(path.is_file(), 'Missing retained input or source: '+str(path))
    return path


def checked_source(workspace, path, digest, size=None):
    path=source_path(workspace,path); raw=path.read_bytes()
    require(sha(raw)==digest and (size is None or len(raw)==size), 'Changed pinned source: '+str(path))
    return path,raw


@contextmanager
def catalogue(workspace, campaign):
    """Load exact checked source bytes, never stale bytecode or another workspace's modules."""
    require(not sys.flags.optimize, 'Run without Python -O; the frozen catalogue uses assertions')
    require(campaign in CATALOGUES, 'Unknown campaign')
    workspace=Path(workspace).resolve(); pilot=workspace/'k60-pilot'
    relative,digest=CATALOGUES[campaign]
    path,raw=checked_source(workspace,pilot/relative,digest)
    manifest=json.loads(raw); sources={}
    records=manifest['files'] if campaign=='closure' else manifest['recipe_files']
    base=pilot if campaign=='closure' else path.parent
    for pin in records:
        if pin['path'].endswith('.py'):
            p,data=checked_source(workspace,base/pin['path'],pin['sha256'],pin.get('bytes'))
            sources[p]=(data,pin['sha256'])
    module_name=campaign+'_catalogue'
    order=[]
    if campaign!='closure':
        for name,(relative,expected) in HELPERS.items():
            p,data=checked_source(workspace,workspace/relative,expected)
            sources[p]=(data,expected);order.append((name,p))
        order += [('uniform_k61',workspace/'r3333-upper-bound/reproduce/uniform_k61.py'),
                  ('generate',pilot/'generate.py')]
    order.append((module_name,pilot/(module_name+'.py')))
    require(all(p in sources for _,p in order), 'Catalogue import is not pinned by the frozen manifest')
    saved={name:sys.modules.get(name) for name,_ in order}; search=list(sys.path)
    try:
        for name,p in order:
            module=types.ModuleType(name);module.__file__=str(p);module.__package__=''
            sys.modules[name]=module
            exec(compile(sources[p][0],str(p),'exec'),module.__dict__)
        result=sys.modules[module_name].Catalogue(path)
        require(result.manifest_sha256==digest, 'Loaded a different catalogue')
        yield result
        for p,(_,expected) in sources.items():
            require(sha(p.read_bytes())==expected, 'Source changed during export: '+str(p))
    finally:
        sys.path[:]=search
        for name,old in saved.items():
            if old is None:sys.modules.pop(name,None)
            else:sys.modules[name]=old


def find_case(cat, case_id):
    matches=[row for row in cat.cases if row['id']==case_id]
    require(len(matches)==1, 'Unknown or nonunique case ID: '+case_id)
    return matches[0]


def export(cat, case_id, output):
    output=Path(output).absolute()
    require(not output.exists() and not output.is_symlink(), 'Refusing to overwrite: '+str(output))
    require(output.parent.is_dir(), 'Output parent directory must already exist')
    row=find_case(cat,case_id)
    raw=cat.cnf_bytes(row) if hasattr(cat,'cnf_bytes') else b''.join(cat.parts(row))
    require(type(raw) is bytes and sha(raw)==row['sha256'], 'Materialized full CNF hash differs from the declared case')
    require(raw.split(b'\n',1)[0]==f'p cnf {row["variables"]} {row["clauses"]}'.encode(), 'Wrong DIMACS header')
    created=None
    try:
        with output.open('xb') as stream:
            created=os.fstat(stream.fileno())
            stream.write(raw);stream.flush();os.fsync(stream.fileno())
        require(sha(output.read_bytes())==row['sha256'], 'Written full CNF hash mismatch')
    except BaseException:
        if created is not None:
            try:
                current=output.lstat()
                if (current.st_dev,current.st_ino)==(created.st_dev,created.st_ino):output.unlink()
            except FileNotFoundError:
                pass
        raise
    return {'case_id':case_id,'owner':row['owner'],'output':str(output),'sha256':row['sha256'],
            'bytes':len(raw),'variables':row['variables'],'clauses':row['clauses'],
            'catalogue_sha256':cat.manifest_sha256,'solver_executed':False}


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--workspace',type=Path,required=True,help='Root containing k60-pilot and r3333-upper-bound')
    p.add_argument('--campaign',choices=CATALOGUES,required=True)
    action=p.add_mutually_exclusive_group(required=True)
    action.add_argument('--case-id');action.add_argument('--list-ids',action='store_true')
    p.add_argument('--output',type=Path)
    p.add_argument('--prefix',default='',help='Optional case-ID prefix when listing')
    p.add_argument('--limit',type=int,default=20,help='Maximum listed IDs (default20)')
    a=p.parse_args()
    try:
        require(a.limit>0, 'List limit must be positive')
        require((a.output is not None)==bool(a.case_id), '--output is required only with --case-id')
        require(a.list_ids or not a.prefix, '--prefix is only valid with --list-ids')
        if a.output is not None:
            require(not a.output.exists() and not a.output.is_symlink(), 'Refusing to overwrite: '+str(a.output))
        with catalogue(a.workspace,a.campaign) as cat:
            if a.list_ids:
                count=0
                for row in cat.cases:
                    if row['id'].startswith(a.prefix):
                        print(row['id']);count+=1
                        if count==a.limit:break
            else:
                result=export(cat,a.case_id,a.output)
        if not a.list_ids:print(json.dumps(result,indent=2))
        return 0
    except Exception as e:
        print(json.dumps({'passed':False,'error':str(e),'solver_executed':False}),file=sys.stderr)
        return 2


if __name__=='__main__':sys.exit(main())
