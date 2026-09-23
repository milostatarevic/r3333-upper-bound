#!/usr/bin/env python3
"""Reproduce all 1,358 UUQ bindings from explicit, relocated input directories."""
import sys
if not __debug__:
    raise SystemExit('ERROR: optimized Python (-O/-OO) is unsupported; run ordinary Python 3.')
import argparse
import hashlib
import json
import re
from pathlib import Path

FAMILIES = {
    'P15_MATRIX_ONLY_189': (189, 91, 'four'),
    'D9_STRONG_ROOT2': (72, 95, 'five'),
    'D9_TWISTED_ROOT1': (132, 95, 'five'),
    'D9_TWISTED_ROOT4': (132, 95, 'five'),
    'D9_TWISTED_ROOT12': (72, 95, 'five'),
    'D10_B2P15_82': (82, 105, 'five'),
}

class Rejected(Exception):
    pass

def require(condition, message):
    if not condition:
        raise Rejected(message)

def sha(data):
    return hashlib.sha256(data).hexdigest()

def unique_pairs(pairs):
    obj = {}
    for k, v in pairs:
        require(k not in obj, 'Duplicate JSON key: '+str(k))
        obj[k] = v
    return obj

def parse_json(data):
    return json.loads(data, object_pairs_hook=unique_pairs)

def immutable_json(path, obj):
    with path.open('x', encoding='utf-8') as stream:
        json.dump(obj, stream, indent=2, sort_keys=True)
        stream.write('\n')
    path.chmod(0o444)

def inside(root, relative):
    p = Path(relative)
    require(not p.is_absolute() and '..' not in p.parts, 'Non-relative reference path: '+relative)
    resolved = (root / p).resolve()
    require(resolved.is_relative_to(root), 'Reference escapes its supplied root: '+relative)
    require(resolved.is_file(), 'Missing file: '+str(root/p))
    return resolved

def rows_tsv(data, count, units, name):
    require(data.endswith(b'\n'), name+': missing terminal newline')
    lines = data.decode('ascii').splitlines()
    require(len(lines) == count, name+': wrong row count')
    rows = []
    for i, line in enumerate(lines):
        tokens = line.split('\t')
        require(tokens[0] == str(i) and len(tokens) == units+1, name+': wrong index/unit count at '+str(i))
        require(all(re.fullmatch(r'-?[1-9][0-9]*', x) for x in tokens[1:]), name+': noncanonical literal')
        rows.append([int(x) for x in tokens[1:]])
    return rows

def verify(args, index_data):
    reference = parse_json(index_data)
    require(reference['schema'] == 'UUQ_NATIVE_REPRODUCTION_REFERENCE_V1', 'Unknown reference schema')
    require(reference['total_cases'] == 1358, 'Wrong reference total')
    require(reference['owners'] == {'UUU': False, 'UUT': True}, 'Wrong Q-type mapping')
    require(set(reference['families']) == set(FAMILIES), 'Wrong family boundary')
    pins = []
    cache = {}
    def archive(relative):
        if relative not in cache:
            data = inside(args.archive_dir, relative).read_bytes()
            want = reference['archive_files'][relative]
            require(sha(data) == want['sha256'] and len(data) == want['bytes'], 'Archive identity mismatch: '+relative)
            cache[relative] = data
            pins.append({'root': 'archive', 'path': relative, 'sha256': sha(data), 'bytes': len(data)})
        return cache[relative]
    def emission(name, expected):
        data = inside(args.emission_dir, name).read_bytes()
        require(sha(data) == expected, 'Emission identity mismatch: '+name)
        pins.append({'root': 'emission', 'path': name, 'sha256': sha(data), 'bytes': len(data)})
        return data
    manifest = parse_json(archive(reference['uut_manifest']))
    manifest_cases = {x['case_id']: x for x in manifest['cases']}
    require(len(manifest_cases) == len(manifest['cases']) == 679, 'UUT manifest is not an exact679 census')
    mappings = {}
    prefix_bodies = {}
    for component, (nv, nc) in {'four': (4900,87311), 'five': (131570,343368)}.items():
        meta = reference['components'][component]
        require(meta['native_variables'] == nv and meta['base_clauses'] == nc, 'Wrong base census')
        mapping = parse_json(archive(meta['mapping']))['dense_to_sparse']
        require(len(mapping) == nv+1 and mapping[0] == 0 and len(set(mapping)) == len(mapping), 'Invalid dense map')
        mappings[component] = mapping
        for owner in ['UUU', 'UUT']:
            key = owner+'_'+component
            pre = reference['prefixes'][key]
            body = inside(args.d_prefix_dir, pre['native_body_file']).read_bytes()
            require(sha(body) == pre['native_body_sha256'], 'Native prefix identity mismatch: '+key)
            pins.append({'root':'d_prefix','path':pre['native_body_file'],'sha256':sha(body),'bytes':len(body)})
            lines = body.decode('ascii').splitlines()
            require(body.endswith(b'\n') and len(lines) == nc, 'Wrong prefix clause count: '+key)
            sparse_lines = []
            for line in lines:
                ts = line.split(' ')
                require(ts[-1] == '0' and all(re.fullmatch(r'-?[1-9][0-9]*', x) for x in ts[:-1]), 'Malformed prefix clause')
                vs = [int(x) for x in ts[:-1]]
                require(all(0 < abs(x) <= nv for x in vs), 'Out-of-range prefix literal')
                sparse_lines.append(' '.join(str((1 if x>0 else -1)*mapping[abs(x)]) for x in vs)+' 0\n')
            sparse_body = ''.join(sparse_lines).encode('ascii')
            sparse_header = f"p cnf {meta['sparse_variables']} {nc}\n".encode('ascii')
            require(sha(sparse_header+sparse_body) == pre['sparse_base_sha256'], 'Sparse base round-trip mismatch: '+key)
            if owner == 'UUT':
                require(sparse_header+sparse_body == archive(meta['uut_sparse_base']), 'Archived UUT sparse base mismatch')
            prefix_bodies[key] = (body, sparse_body)
    reference_cases = {}
    for row in reference['cases']:
        key = (row['owner'], row['family'], row['local_index'])
        require(key not in reference_cases, 'Duplicate reference case')
        require(row['q'] == (row['owner']=='UUT') and row['owner'] in ('UUU','UUT'), 'Wrong owner/Q identity')
        reference_cases[key] = row
    require(len(reference_cases) == 1358, 'Incomplete reference cases')
    results = []
    used_manifest = set()
    for family, (count, units, component) in FAMILIES.items():
        spec = reference['families'][family]
        require((spec['count'],spec['units'],spec['component']) == (count,units,component), 'Wrong family shape')
        census = parse_json(archive(spec['census']))['cases']
        require(len(census) == count and len({c['case_id'] for c in census}) == count, 'Incomplete/duplicate census')
        sparse_rows = rows_tsv(emission(family+'_SPARSE.tsv',spec['sparse_emission_sha256']),count,units,family+' sparse')
        native_rows = rows_tsv(emission(family+'_NATIVE.tsv',spec['native_emission_sha256']),count,units,family+' native')
        mapping = mappings[component]
        meta = reference['components'][component]
        for i, (case, sparse, native) in enumerate(zip(census, sparse_rows, native_rows)):
            require(case['family']==family, 'Wrong census family')
            if family == 'D10_B2P15_82':
                require(case['leaf_index']==i and 'expected_formula' in case, 'Wrong original D10 leaf index')
            else:
                require(sparse == case['units'], 'Sparse suffix differs from original census: '+case['case_id'])
            require(all(0<abs(v)<len(mapping) for v in native), 'Native suffix variable outside boundary')
            require([(1 if v>0 else -1)*mapping[abs(v)] for v in native] == sparse, 'Native map changes a suffix literal')
            mc = manifest_cases[case['case_id']]
            require(mc['family']==family and mc['units']==sparse, 'UUT source census differs')
            used_manifest.add(case['case_id'])
            suffix = ''.join(f'{v} 0\n' for v in native).encode('ascii')
            sparse_suffix = ''.join(f'{v} 0\n' for v in sparse).encode('ascii')
            clauses = meta['base_clauses']+units
            for owner in ['UUU','UUT']:
                expected = reference_cases[(owner,family,i)]
                require(expected['case_id']==case['case_id'], 'Wrong reference leaf ordering')
                dense_body, sparse_body = prefix_bodies[owner+'_'+component]
                dense_hash = sha(f"p cnf {meta['native_variables']} {clauses}\n".encode()+dense_body+suffix)
                sparse_hash = sha(f"p cnf {meta['sparse_variables']} {clauses}\n".encode()+sparse_body+sparse_suffix)
                require(dense_hash==expected['native_sha256'] and sparse_hash==expected['sparse_sha256'], 'Full formula hash mismatch: '+owner+'/'+case['case_id'])
                record = parse_json(archive(expected['result']))
                require(record['status']=='UNSAT', 'Native result is not UNSAT')
                if owner == 'UUU':
                    require(record['case_id']==case['case_id'] and record['solver_exit_code']==20, 'Wrong UUU terminal identity')
                    if family == 'D10_B2P15_82':
                        require(case['expected_formula']['dense_sha256']==dense_hash and case['expected_formula']['sparse_sha256']==sparse_hash, 'Original D10 census hash mismatch')
                    require(record['materialize']['dense_sha256']==dense_hash and record['materialize']['sparse_sha256']==sparse_hash, 'UUU solver input hash mismatch')
                    require(mc['old_virtual_dense_sha256']==dense_hash and mc['old_virtual_sparse_sha256']==sparse_hash, 'Original UUU manifest binding mismatch')
                else:
                    require(record['native']['returncode']==20 and record['reaped'] is True and record['terminal']['status_line']=='UNSATISFIABLE', 'Wrong UUT terminal result')
                    require(record['input']['census']['sha256']==dense_hash and record['input_posthash']['sha256']==dense_hash, 'UUT solver input hash mismatch')
                    require(mc['cnf_sha256']==dense_hash and mc['uut_sparse_virtual_sha256']==sparse_hash, 'UUT manifest binding mismatch')
                results.append({'q':owner=='UUT','owner':owner,'family':family,'local_index':i,'case_id':case['case_id'],'native_sha256':dense_hash,'sparse_sha256':sparse_hash,'result_reference':expected['result']})
    require(len(results)==1358 and used_manifest==set(manifest_cases), 'Incomplete final cover')
    require(set(cache)==set(reference['archive_files']), 'Unconsumed archived reference files')
    return results, pins

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--archive-dir',type=Path,required=True,help='Extracted evidence directory containing D/UUU and D/UUT')
    parser.add_argument('--emission-dir',type=Path,required=True)
    parser.add_argument('--d-prefix-dir',type=Path,required=True)
    parser.add_argument('--output-dir',type=Path,required=True,help='Must not already exist')
    parser.add_argument('--reference-index',type=Path,default=Path(__file__).with_name('reference_index.json'))
    args = parser.parse_args()
    for name in ['archive_dir','emission_dir','d_prefix_dir']:
        p = getattr(args,name).resolve()
        if name == 'archive_dir' and not (p/'D').is_dir() and (p/'evidence/D').is_dir():
            p = (p/'evidence').resolve()
        require(p.is_dir(), 'Missing directory: '+str(p))
        setattr(args,name,p)
    require(not args.output_dir.exists(), 'Output directory must be fresh')
    args.output_dir.mkdir(parents=True,exist_ok=False)
    try:
        index_data = args.reference_index.read_bytes()
        results,pins = verify(args,index_data)
        index = {'schema':'UUQ_REPRODUCTION_PATH_HASH_INDEX_V1','reference_sha256':sha(index_data),'tool_sha256':sha(Path(__file__).read_bytes()),'roots':{k:str(getattr(args,k)) for k in ['archive_dir','emission_dir','d_prefix_dir']},'files':pins}
        immutable_json(args.output_dir/'PATH_HASH_INDEX.json',index)
        immutable_json(args.output_dir/'BINDING.json',{'status':'PASS','cases':1358,'native_solver_runs':0,'certificate_replays':0,'mathematical_endpoint':'PricingG.UUQExactNative.actual_UU_native','emission_equality':'PricingG.UUQEmissionIdentity.emitted_eq','path_hash_index_sha256':sha((args.output_dir/'PATH_HASH_INDEX.json').read_bytes()),'rows':results})
        print('PASS: 1,358 exact sparse/native formulas and retained UNSAT input identities.')
        return 0
    except Exception as error:
        immutable_json(args.output_dir/'REJECTED.json',{'status':'REJECTED','error':str(error),'error_type':type(error).__name__})
        raise

if __name__=='__main__':
    try:
        raise SystemExit(main())
    except (Rejected,ValueError,KeyError,OSError) as error:
        print('REJECTED: '+str(error),file=sys.stderr)
        raise SystemExit(1)
