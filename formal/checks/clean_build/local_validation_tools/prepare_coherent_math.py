#!/usr/bin/env python3
"""Freeze a transitive source closure; reuse only established classification/library code.

May append new roots when every previously frozen source remains byte-identical.
It never imports prior incremental mathematical outputs into the clean build.
"""
import argparse, hashlib, json, pathlib, re, sys
P = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(P))
from resource_gate import sha, utc, write_json
R = P.parents[1] / 'ramsey61-provisional-staging'
CLASS = R / 'classification/.lake/classification_runs/20260922T072158Z_1790061718513440000/lib/lean'
ap = argparse.ArgumentParser()
ap.add_argument('--name', default='coherent_math_001')
ap.add_argument('roots', nargs='+')
a = ap.parse_args()
assert re.fullmatch(r'coherent_math_[0-9]+', a.name)
B = P / a.name
B.mkdir(exist_ok=True)
for x in ['src','lib','external_classification','runs','manifests']:
    (B/x).mkdir(exist_ok=True)
old = json.loads((B/'MANIFEST.json').read_text()) if (B/'MANIFEST.json').exists() else None
roots = sorted(set(a.roots + (old['roots'] if old else [])))
lookup = [P/x for x in ['integration','abd','c','g']] + [R/'formal',R/'classification',R/'classification/adapter']
seen, libraries = {}, set()
allowed = {'Mathlib','Std','Lean','Init','Batteries','Aesop','Qq','Plausible','ImportGraph','ProofWidgets','LeanSearchClient'}

def visit(m):
    if m in seen or m in libraries: return
    rel = pathlib.Path(*m.split('.')).with_suffix('.lean')
    source = next((x/rel for x in lookup if (x/rel).is_file()),None)
    if source is None:
        if m.split('.')[0] in allowed:
            libraries.add(m); return
        raise RuntimeError('Unresolved project source '+m)
    text = source.read_text()
    imports = []
    for line in re.findall(r'^\s*(?:public )?import\s+([^\n]+)',text,re.M):
        imports.extend(t for t in line.split() if re.fullmatch(r'[A-Za-z_][A-Za-z_0-9.]*',t))
    classification = source.is_relative_to(R/'classification')
    if not classification and re.search(r'^\s*#eval\b|^\s*checked_lrat_proof\b',text,re.M):
        raise RuntimeError('Execution/certificate directive in build closure: '+m)
    row = {'module':m,'source':str(source),'sha256':sha(source),'bytes':source.stat().st_size,
           'imports':imports,'kind':'established_classification' if classification else 'clean_math'}
    seen[m] = row
    for d in imports: visit(d)

for m in roots: visit(m)
if old:
    for m,v in old['modules'].items():
        assert m in seen and seen[m]['sha256']==v['sha256'], 'Frozen source changed: '+m

# Admission estimates use measured successful peaks, not execution caps.
estimates = {}
for baseline in json.loads((P/'BASELINE_DEPENDENCIES.json').read_text())['modules']:
    if baseline['module'] in seen:
        estimates[baseline['module']]=baseline.get('peak_RSS_bytes',0)
for lane in ['integration','abd','g','c']:
    for root in [P/lane/'runs',P.parent/'ramsey61_math_formalization_pricing_20260922_001'/lane/'runs']:
        for receipt in root.glob('*/receipt.json'):
            d = json.loads(receipt.read_text())
            if d.get('status') == 'PASS' and d.get('module') in seen:
                m=d['module'];peak=d.get('peak_polled_RSS_bytes') or d.get('peak_RSS_bytes') or 0
                estimates[m]=max(estimates.get(m,0),peak)
for m,row in seen.items():
    rel=pathlib.Path(*m.split('.'))
    if row['kind']=='clean_math':
        dest=(B/'src'/rel).with_suffix('.lean');dest.parent.mkdir(parents=True,exist_ok=True)
        if dest.exists(): assert sha(dest)==row['sha256']
        else: dest.write_bytes(pathlib.Path(row['source']).read_bytes());dest.chmod(0o444)
        row['frozen_source']=str(dest)
        row['expected_RSS_GiB']=max(4,estimates.get(m,0)/1024**3*1.25+1)
    else:
        artifact=(CLASS/rel).with_suffix('.olean')
        assert artifact.is_file(), 'Missing established classification '+m
        row['artifact']=str(artifact.resolve());row['artifact_sha256']=sha(artifact)
        dest=(B/'external_classification'/rel).with_suffix('.olean');dest.parent.mkdir(parents=True,exist_ok=True)
        if not dest.exists(): dest.symlink_to(artifact)
        assert sha(dest)==row['artifact_sha256']
        # Lean resolves the first namespace directory, not individual missing modules.
        merged=(B/'lib'/rel).with_suffix('.olean');merged.parent.mkdir(parents=True,exist_ok=True)
        if not merged.exists(): merged.symlink_to(artifact)
        assert sha(merged)==row['artifact_sha256']
mathlib_overlay=R/'formal/.lake/build/lib/lean/Mathlib'
if not (B/'lib/Mathlib').exists(): (B/'lib/Mathlib').symlink_to(mathlib_overlay,target_is_directory=True)
manifest={'created_utc':utc(),'Mathlib_overlay':str(mathlib_overlay),'roots':roots,'modules':seen,'external_library_imports':sorted(libraries),
          'publication_commit':'b51b57b0d74dc4c262634f2395d9b7f4254f1cc0',
          'scope':'Coherent rebuild of all mathematical source dependencies except established classification library; no SAT/certificate executions, no incremental probe outputs in import path.',
          'prepare_script_sha256':sha(__file__)}
archive=B/'manifests'/f'manifest_{len(list((B/"manifests").glob("*.json"))):03}.json'
write_json(archive,manifest);write_json(B/'MANIFEST.json',manifest)
print(json.dumps({'manifest':str(archive),'modules':len(seen),
                  'clean_math':sum(x['kind']=='clean_math' for x in seen.values()),
                  'source_bytes':sum(x['bytes'] for x in seen.values())}))
