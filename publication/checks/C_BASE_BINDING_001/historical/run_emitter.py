from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,time
ROOT=Path(__file__).resolve().parent
FORMAL=Path('/Users/milostatarevic/programming/projects/ramsey-diagonal/r77-findings/ramsey61-provisional-staging/formal')
CACHE=Path('/Users/milostatarevic/programming/projects/ramsey-increment-theorem/lean/.lake/packages')
LEAN=Path('/Users/milostatarevic/.elan/toolchains/leanprover--lean4---v4.32.1/bin/lean')
SOURCE=ROOT/'EmitBase.lean';OUT=ROOT/'BROAD_BASE_FROM_LEAN.cnf'
def pin(p):return {'path':str(p),'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
def host():
 text=subprocess.run(['/usr/bin/memory_pressure','-Q'],check=True,capture_output=True,text=True).stdout
 m=re.search(r'System-wide memory free percentage:\s*(\d+)%',text)
 if not m:raise RuntimeError('pressure reading unavailable')
 return {'memory_free_percent':int(m[1]),'disk_free_bytes':shutil.disk_usage(ROOT).free,'pressure_report':text}
if any((ROOT/name).exists() for name in ['claim.json','receipt.json','lean.log','BROAD_BASE_FROM_LEAN.cnf']):raise RuntimeError('create-only run already exists')
before=host()
if before['memory_free_percent']<=5 or before['disk_free_bytes']<(1<<30):raise RuntimeError('actual host pressure: no new compiler admission')
pins={'emitter':pin(SOURCE),'controller':pin(Path(__file__)),'lean':pin(LEAN),'imports':[]}
for name in ['CEncodingBase','CEncodingCore','DenseCounter','Selector','Incidence','Profiles','Foundations']:
 pins['imports'].append({'source':pin(FORMAL/'Ramsey61'/f'{name}.lean'),'olean':pin(FORMAL/'.lake/build/lib/lean/Ramsey61'/f'{name}.olean')})
env=dict(os.environ,LEAN_PATH=os.pathsep.join(map(str,[FORMAL/'.lake/build/lib/lean']+[p/'.lake/build/lib/lean' for p in sorted(CACHE.iterdir()) if p.is_dir()])))
command=[str(LEAN),'-j1','--run',str(SOURCE),str(OUT)]
(ROOT/'claim.json').write_text(json.dumps({'command':command,'host_before':before,'inputs':pins,'CPU_limit':None,'RSS_kill_limit':None,'file_size_limit':None},indent=2)+'\n')
start=time.monotonic()
with (ROOT/'lean.log').open('x') as f:result=subprocess.run(['/usr/bin/time','-l']+command,cwd=FORMAL,env=env,stdout=f,stderr=subprocess.STDOUT)
text=(ROOT/'lean.log').read_text();timing=re.search(r'([\d.]+) real\s+([\d.]+) user\s+([\d.]+) sys',text);rss=re.search(r'(\d+)\s+maximum resident set size',text)
record={'status':'EMITTED_PENDING_COMPARISON' if result.returncode==0 else 'FAIL','exit_code':result.returncode,'user_CPU_seconds':float(timing[2]) if timing else None,'system_CPU_seconds':float(timing[3]) if timing else None,'peak_RSS_bytes_macos':int(rss[1]) if rss else None,'elapsed_seconds':time.monotonic()-start,'inputs':pins,'output':pin(OUT) if OUT.exists() else None,'log':pin(ROOT/'lean.log'),'host_before':before,'host_after':host(),'CPU_limit':None,'RSS_kill_limit':None,'file_size_limit':None,'cache_writes_requested':False,'new_solver_calls':0}
(ROOT/'receipt.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({k:record[k] for k in ['status','user_CPU_seconds','system_CPU_seconds','peak_RSS_bytes_macos','elapsed_seconds','output']}));print(text)
raise SystemExit(result.returncode)
