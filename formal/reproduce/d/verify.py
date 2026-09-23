#!/usr/bin/env python3
"""Bind the twelve Lean native D prefixes to the frozen archive. No solver calls."""
import argparse, datetime, hashlib, json, pathlib, sys
if not __debug__:
    raise SystemExit('Python optimization mode is prohibited: assertions are part of verification')
ap=argparse.ArgumentParser()
ap.add_argument('--archive-dir',required=True,type=pathlib.Path)
ap.add_argument('--d-prefix-dir',required=True,type=pathlib.Path)
ap.add_argument('--output-dir',required=True,type=pathlib.Path)
a=ap.parse_args()
archive=a.archive_dir
if (archive/'evidence').is_dir(): archive=archive/'evidence'
pins=json.loads(pathlib.Path(__file__).with_name('path_index.json').read_text())
def sha(b): return hashlib.sha256(b).hexdigest()
def load(relative):
    p=archive/relative;b=p.read_bytes()
    assert relative in pins and sha(b)==pins[relative]['sha256'], 'Archive pin mismatch: '+relative
    return json.loads(b)
assert not a.output_dir.exists(),'Output directory must be fresh'
rows=[]
for kind in ['UTU','UTT','TTU','TTT']:
    base=f'D/mixed/full_inputs_{kind}_000'
    manifest=load(base+'/MANIFEST.json')
    for stage,p in manifest['prefixes'].items():
        shape=p['base_contract']['component']
        native=(archive/base/pathlib.Path(p['path']).name).read_bytes()
        assert sha(native)==p['sha256']
        header,body=native.split(b'\n',1)
        got=(a.d_prefix_dir/f'{kind}_{shape}.body').read_bytes()
        assert got==body and sha(got)==p['body_sha256'],kind+'/'+shape
        assert got.count(b'\n')==p['base_clauses']
        assert header==f"p cnf {p['variables']} {p['clauses']}".encode()
        rows.append({'kind':kind,'shape':shape,'stage':stage,'body_sha256':sha(got),
                     'body_bytes':len(got),'comparison':'exact archived ordered bytes'})
d=load('D/UUT/full_inputs_000/MANIFEST.json')
for shape,p in d['parents'].items():
    for kind,key in [('UUU','original_dense_body_sha256'),('UUT','uut_dense_body_sha256')]:
        got=(a.d_prefix_dir/f'{kind}_{shape}.body').read_bytes()
        assert sha(got)==p[key],kind+'/'+shape
        assert got.count(b'\n') in (87311,343368)
        rows.append({'kind':kind,'shape':shape,'body_sha256':sha(got),
                     'body_bytes':len(got),'comparison':'pinned archived dense base hash'})
assert len({(r['kind'],r['shape']) for r in rows})==12
a.output_dir.mkdir(parents=True)
receipt={'status':'PASS_ALL_TWELVE_NATIVE_D_BASES','created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
         'script_sha256':sha(pathlib.Path(__file__).read_bytes()),'input_index':pins,'rows':rows,
         'scope':'Native D base identities only. Complete UUQ and common-case comparators separately verify full formula/input/result identities.'}
with (a.output_dir/'receipt.json').open('x') as f:json.dump(receipt,f,indent=2);f.write('\n')
print(receipt['status'])
