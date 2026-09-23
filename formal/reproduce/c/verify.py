#!/usr/bin/env python3
"""Verify all456 exact Lean C suffixes and complete native input hashes; no solving."""
from pathlib import Path
import argparse,collections,datetime,hashlib,json,sys,time
if not __debug__:
    raise SystemExit('Python optimization is prohibited: assertions are part of verification')
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--archive-dir',required=True,type=Path,help='Extracted archive root or its evidence/ directory')
p.add_argument('--emission-dir',required=True,type=Path,help='Fresh suffixes emitted by Emit.lean')
p.add_argument('--base-file',required=True,type=Path,help='Pinned BROAD_BASE_001.cnf or byte-identical Lean base emission')
p.add_argument('--output-dir',required=True,type=Path,help='Fresh receipt directory')
a=p.parse_args();started=time.process_time();archive=a.archive_dir.resolve(strict=True)
if (archive/'evidence').is_dir():archive=archive/'evidence'
base_file=a.base_file.resolve(strict=True);emission=a.emission_dir.resolve(strict=True)
a.output_dir.mkdir(parents=True,exist_ok=False)
pins=[]
def sha(b):return hashlib.sha256(b).hexdigest()
def read(p,expected=None):
    p=Path(p);b=p.read_bytes();h=sha(b)
    if expected is not None:assert h==expected,('hash mismatch',str(p),h,expected)
    pins.append({'path':str(p),'sha256':h,'bytes':len(b)});return b

def unique(pairs):
    d={}
    for k,v in pairs:
        assert k not in d,('duplicate JSON key',k)
        d[k]=v
    return d

def jread(p,expected=None):return json.loads(read(p,expected),object_pairs_hook=unique)
index_path=Path(__file__).with_name('path_index.json');index=jread(index_path)
assert index['schema']=='ramsey61-c456-portable-index-v1'
package=Path(__file__).resolve().parent
provenance=index['base_provenance']
original_base=jread(package/provenance['comparison'],provenance['comparison_sha256'])
assert original_base['status']=='PASS' and original_base['clauses_compared']==1880888
assert original_base['emitted_full_file_sha256']==index['base_sha256']
read(package/provenance['base_emitter'],provenance['base_emitter_sha256'])
base=read(base_file,index['base_sha256']);header,body=base.split(b'\n',1)
assert header==b'p cnf 439723 1880888' and body.count(b'\n')==1880888
seeds=jread(archive/'c_campaign/inputs/SEEDS.json',index['seeds_json_sha256'])['seeds']
assert len(seeds)==len(index['rows'])==456
expected_files={f'R3_{i}.units'for i in range(456)}
assert {p.name for p in emission.iterdir()}==expected_files, 'Suffix file census mismatch'
states={};rows=[];record_statuses=collections.Counter();unit_count=0
for i,(seed,expected) in enumerate(zip(seeds,index['rows'])):
    assert seed['id']==expected['case_id']==f'R3_{i:03d}' and expected['index']==i
    def edge(triple):
        u,v,q=triple;assert all(type(x)is int for x in triple)
        assert 0<=u<v<61 and 0<=q<4
        return 4*(u*(121-u)//2+v-u-1)+q+1
    literals=[edge(t)for t in seed['unit_colors']]+[-edge(t)for t in seed['non_color']]
    n=len(literals);actual=read(emission/f'R3_{i}.units',expected['suffix_sha256'])
    assert actual==''.join(f'{x} 0\n'for x in literals).encode('ascii'),('ordered literal mismatch',i)
    assert n==expected['units'];unit_count+=n
    if n not in states:
        new_header=f'p cnf 439723 {1880888+n}\n'.encode();state=hashlib.sha256();state.update(new_header);state.update(body);states[n]=(new_header,state)
    new_header,state=states[n];full=state.copy();full.update(actual);full_sha=full.hexdigest();full_bytes=len(new_header)+len(body)+len(actual)
    assert full_sha==expected['full_formula_sha256'] and full_bytes==expected['full_formula_bytes']
    seed_sha=sha(json.dumps(seed,sort_keys=True,separators=(',',':')).encode())
    assert seed_sha==expected['seed_sha256']
    case_records=[];unsat=0
    for record in expected['records']:
        relative=Path(record['path']);assert not relative.is_absolute() and '..'not in relative.parts
        r=jread(archive/relative,record['sha256'])
        assert r['case_id']==seed['id'] and r['seed_sha256']==seed_sha
        assert r['base']['sha256']==index['base_sha256']
        assert r['formula_sha256']==full_sha and r['formula_bytes']==full_bytes
        assert r['variables']==439723 and r['clauses']==1880888+n
        assert r['status']==record['status'] and r['phase']==record['phase']
        if r['status']=='UNSAT':assert r['exit_code']==20;unsat+=1
        else:assert r['status']=='UNKNOWN_CPU_CAP'
        record_statuses[r['status']]+=1
        case_records.append({'path':record['path'],'status':r['status'],'phase':r['phase'],'sha256':record['sha256']})
    assert unsat==2,('expected exactly two retained UNSAT records',seed['id'],unsat)
    rows.append({'case_id':seed['id'],'units':n,'suffix_sha256':sha(actual),'formula_sha256':full_sha,'formula_bytes':full_bytes,'clauses':1880888+n,'records':case_records})
assert unit_count==197544 and dict(record_statuses)=={'UNSAT':912,'UNKNOWN_CPU_CAP':17}
read(Path(__file__));read(Path(__file__).with_name('Emit.lean'))
result={'status':'PASS_ALL_456_NATIVE_C_INPUT_IDENTITIES','created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'cases':456,'unit_clauses':unit_count,'base_sha256':index['base_sha256'],'retained_records':sum(record_statuses.values()),'record_status_counts':dict(record_statuses),'each_case_has_exactly_two_UNSAT_records':True,'CPU_seconds':time.process_time()-started,'scope':'Exact Lean seed suffixes and shared pinned base bind every complete input to the retained native result records. UNKNOWN attempts remain UNKNOWN. Native answers are not certificates.','base_provenance':index['base_provenance'],'rows':rows,'pins':pins,'solver_calls':0,'certificate_replays':0,'complete_case_CNFs_written':0}
with(a.output_dir/'receipt.json').open('x')as f:json.dump(result,f,indent=2);f.write('\n')
print(json.dumps({k:v for k,v in result.items()if k not in ['rows','pins']},indent=2))
