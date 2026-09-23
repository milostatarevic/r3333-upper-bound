#!/usr/bin/env python3
"""Topological clean compilation; scheduling only, compilers acquire shared slots."""
import argparse,concurrent.futures,fcntl,json,pathlib,subprocess,sys,time
P=pathlib.Path(__file__).resolve().parent
sys.path.insert(0,str(P))
from resource_gate import sha,utc,write_json
ap=argparse.ArgumentParser();ap.add_argument('--workers',type=int,choices=range(1,9),default=6);ap.add_argument('name');a=ap.parse_args()
B=P/a.name
lock=(B/'controller.lock').open('a+');fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
manifest=json.loads((B/'MANIFEST.json').read_text());rows=manifest['modules']
done={m for m,r in rows.items() if r['kind']!='clean_math'}
receipts={}
for p in sorted((B/'runs').glob('*/receipt.json')):
    r=json.loads(p.read_text());m=r.get('module')
    if m in rows and r['status']=='PASS' and r['source_sha256']==rows[m]['sha256']:
        artifact=(B/'lib'/pathlib.Path(*m.split('.'))).with_suffix('.olean')
        if artifact.exists() and sha(artifact)==r['output_sha256']:
            receipts[m]=r;done.add(m)
pending=set(rows)-done;active={};failures={};started=utc()
def compile_one(m):
    return subprocess.run([sys.executable,'-I','-B',str(P/'coherent_math_one.py'),B.name,m],
                          stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
with concurrent.futures.ThreadPoolExecutor(max_workers=a.workers) as pool:
    while pending or active:
        ready=sorted(m for m in pending if all(d in done or d not in rows for d in rows[m]['imports']))
        for m in ready[:a.workers-len(active)]:
            active[pool.submit(compile_one,m)]=m;pending.remove(m)
        if not active: break
        ended,_=concurrent.futures.wait(active,timeout=5,return_when=concurrent.futures.FIRST_COMPLETED)
        for fut in ended:
            m=active.pop(fut);result=fut.result()
            if result.returncode==0:done.add(m)
            else:failures[m]=result.stdout
            print(result.stdout.rstrip(),flush=True)
        write_json(B/'STATUS.json',{'started_utc':started,'updated_utc':utc(),
            'done':len(done),'total':len(rows),'active':list(active.values()),
            'pending':len(pending),'failures':failures})
    status='PASS' if not pending and not failures else 'INCOMPLETE'
    write_json(B/'BUILD_RESULT.json',{'status':status,'started_utc':started,'finished_utc':utc(),
        'done':len(done),'total':len(rows),'pending':sorted(pending),'failures':failures,
        'manifest_sha256':sha(B/'MANIFEST.json'),'controller_sha256':sha(__file__)})
result_bytes=(B/'BUILD_RESULT.json').read_bytes()
archive=B/'manifests'/('build_result_'+str(len(list((B/'manifests').glob('build_result_*.json')))).zfill(3)+'.json')
archive.write_bytes(result_bytes)
print(status,flush=True)
sys.exit(0 if status=='PASS' else 1)
