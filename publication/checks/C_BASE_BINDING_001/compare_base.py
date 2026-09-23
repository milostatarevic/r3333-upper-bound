from pathlib import Path
import argparse,hashlib,json,time,resource
if not __debug__:raise RuntimeError('run without Python optimization: assertions are required')
parser=argparse.ArgumentParser(description="Compare Lean-emitted C base with the exact archived formula; no solver is run.")
parser.add_argument('--archived',required=True,type=Path)
parser.add_argument('--emitted',required=True,type=Path)
parser.add_argument('--output',required=True,type=Path)
args=parser.parse_args()
BASE=args.archived
EMITTED=args.emitted
OUTPUT=args.output
if OUTPUT.resolve()in (BASE.resolve(),EMITTED.resolve()):raise RuntimeError('output must differ from input paths')
PIN='58478e3641d3ea52639566683daaea5f7a1d4112de5809f4af73ce1dfebf164f'
COUNTS=[('physical_edge_exactly_one',12810),('all_physical_nonmonochromatic_triangles',143960),('degree_prefix_equivalences',972828),('degree_at_most_sixteen',244),('genuine_directed_highness_equivalences',29280),('H_prefix_equivalences',693265),('ordered_profile_equivalences',19276),('selector_X_exclusions',1708),('physical_root_spokes_and_H',61),('regime3_fiber_prefix_equivalences',7456)]
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1<<20),b''):h.update(b)
 return h.hexdigest()
if OUTPUT.exists():raise RuntimeError('create-only result already exists')
start=time.process_time();wall=time.monotonic()
assert BASE.stat().st_size==39604154 and sha(BASE)==PIN
assert EMITTED.stat().st_size==39604154 and sha(EMITTED)==PIN
failures=[];rows=[];line_number=0;total_hash=hashlib.sha256();observed_vars=set()
with BASE.open('rb') as base,EMITTED.open('rb') as emitted:
 assert base.readline()==emitted.readline()==b'p cnf 439723 1880888\n'
 for name,count in COUNTS:
  a_hash=hashlib.sha256();b_hash=hashlib.sha256();width=0;maxvar=0;sectionbytes=0
  for _ in range(count):
   line_number+=1;a=base.readline();b=emitted.readline();assert a and b
   a_hash.update(a);b_hash.update(b);total_hash.update(b);sectionbytes+=len(b)
   if a!=b and len(failures)<20:failures.append({'body_clause':line_number,'expected':a.decode(),'emitted':b.decode()})
   tokens=b.split();assert tokens and tokens[-1]==b'0'
   literals=[int(x) for x in tokens[:-1]];assert all(x!=0 and abs(x)<=439723 for x in literals)
   width=max(width,len(literals));maxvar=max(maxvar,max(map(abs,literals),default=0))
  rows.append({'family':name,'clauses':count,'body_bytes':sectionbytes,'max_clause_width':width,'max_variable':maxvar,'archived_sha256':a_hash.hexdigest(),'emitted_sha256':b_hash.hexdigest(),'byte_identical':a_hash.digest()==b_hash.digest()})
 assert emitted.read(1)==b''
 assert base.read(1)==b''
record={'schema':'RAMSEY61_LEAN_FULL_BASE_IDENTITY_PORTABLE_1','status':'PASS' if not failures and all(x['byte_identical'] for x in rows) else 'FAIL','comparison':'Full DIMACS header and every emitted clause byte compared with the frozen broad base.','clauses_compared':line_number,'clause_order_and_literal_signs_and_numbers_identical':not failures,'families':rows,'emitted_body_sha256':total_hash.hexdigest(),'emitted_full_file_sha256':sha(EMITTED),'archived_full_base_sha256':PIN,'archived_full_base_bytes':BASE.stat().st_size,'archived_path':str(BASE.resolve()),'emitted_path':str(EMITTED.resolve()),'comparison_source_sha256':sha(Path(__file__)),'CPU_seconds':time.process_time()-start,'elapsed_seconds_informational':time.monotonic()-wall,'peak_RSS_raw':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,'mismatches':failures,'semantic_consequence':'All ten emitted clause families are literally identical to the full archived broad base; no semantic weakening or variable renaming is used.','trust_boundary':'The mathematics proves satisfaction of the Lean-defined generator. This is an external execution/byte comparison, not a Lean kernel proof of parsing/serialization/hash equality. It binds the complete deterministic C base; the physical456 seed coverage remains separate.','new_solver_calls':0}
with OUTPUT.open('x') as f:json.dump(record,f,indent=2);f.write('\n')
print(json.dumps({k:record[k] for k in ['status','clauses_compared','CPU_seconds','elapsed_seconds_informational','peak_RSS_raw','mismatches']}))
raise SystemExit(0 if record['status']=='PASS' else 1)
