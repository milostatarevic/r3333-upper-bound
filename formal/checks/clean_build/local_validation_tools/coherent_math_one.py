#!/usr/bin/env python3
"""One isolated compiler process, sharing the authorized eight-worker gate."""
import datetime,json,os,pathlib,sys,uuid
P=pathlib.Path(__file__).resolve().parent
sys.path.insert(0,str(P))
from resource_gate import sha,write_json,run_owned
B=P/sys.argv[1];m=sys.argv[2]
manifest=json.loads((B/'MANIFEST.json').read_text());row=manifest['modules'][m]
assert row['kind']=='clean_math'
source=pathlib.Path(row['frozen_source']);assert sha(source)==row['sha256']
CACHE=pathlib.Path('/Users/milostatarevic/programming/projects/ramsey-increment-theorem/lean/.lake/packages')
LEAN=pathlib.Path('/Users/milostatarevic/.elan/toolchains/leanprover--lean4---v4.32.1/bin/lean')
paths=[B/'lib',B/'external_classification']+[d/'.lake/build/lib/lean' for d in sorted(CACHE.iterdir()) if d.is_dir()]+[LEAN.parents[1]/'lib/lean']
run=B/'runs'/(datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')+'_'+uuid.uuid4().hex[:8]);run.mkdir()
inputs=[]
for dep in row['imports']:
    rel=pathlib.Path(*dep.split('.')).with_suffix('.olean')
    p=next((x/rel for x in paths if (x/rel).is_file()),None)
    assert p is not None,'Missing clean import '+dep
    inputs.append({'module':dep,'path':str(p.resolve()),'sha256':sha(p)})
write_json(run/'inputs.json',inputs)
artifact=run/'output.olean'
env=dict(os.environ,LEAN_PATH=os.pathsep.join(map(str,paths)),LEAN_NUM_THREADS='1',OMP_NUM_THREADS='1',OPENBLAS_NUM_THREADS='1')
r=run_owned([str(LEAN),'-j1','-o',str(artifact),str(source)],B/'src',env,run,
    {'module':m,'source':str(source),'source_sha256':row['sha256'],
     'runner_sha256':sha(__file__),'gate_sha256':sha(P/'resource_gate.py'),
     'lean_sha256':sha(LEAN),'LEAN_PATH':env['LEAN_PATH'],'new_solver_calls':0},row['expected_RSS_GiB'])
if sha(source)!=row['sha256'] or any(sha(x['path'])!=x['sha256'] for x in inputs):
    r.update(status='FAIL',guard_reason='Frozen source or clean import changed')
r.update(artifact=str(artifact),artifact_bytes=artifact.stat().st_size if artifact.exists() else None,
         output_sha256=sha(artifact) if artifact.exists() and r['status']=='PASS' else None)
if r['status']=='PASS':
    dest=(B/'lib'/pathlib.Path(*m.split('.'))).with_suffix('.olean');dest.parent.mkdir(parents=True,exist_ok=True)
    temp=dest.with_name(dest.name+'.'+uuid.uuid4().hex+'.link');temp.symlink_to(artifact);os.replace(temp,dest)
write_json(run/'receipt.json',r)
print(json.dumps({'module':m,'status':r['status'],'CPU_seconds':r['CPU_seconds'],'receipt':str(run/'receipt.json')}),flush=True)
sys.exit(0 if r['status']=='PASS' else 1)
