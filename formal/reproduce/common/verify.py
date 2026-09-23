"""Bind the checked common native family to every archived original input.

No solver, formula mutation, or unproved mathematical-cover assumption. The
Lean emitter supplies concrete admitted owners and ordered signed suffixes.
Already checked Lean prefix bodies supply the remaining clauses. Hash states
are cloned after a prefix, so complete CNFs need not be materialized again.
"""
from pathlib import Path
import argparse, collections, datetime, hashlib, json, re, sys, time

if not __debug__:
    raise SystemExit('Refusing Python optimization: assertions are required.')
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--package-root', type=Path, required=True,
                    help='Portable common tool bundle containing path_index.json')
parser.add_argument('--archive-root', '--archive-dir', dest='archive_root', type=Path, required=True,
                    help='Extracted archive root containing evidence/, or evidence/ itself')
parser.add_argument('--emission-root', type=Path, required=True)
parser.add_argument('--d-prefix-dir', type=Path, required=True)
parser.add_argument('--output-dir', type=Path, required=True, help='Fresh report directory')
args = parser.parse_args()
package = args.package_root.resolve(strict=True)
archive = args.archive_root.resolve(strict=True)
if (archive/'evidence').is_dir():
    archive = archive/'evidence'
emission_root = args.emission_root.resolve(strict=True)
d_prefix_root = args.d_prefix_dir.resolve(strict=True)
output_root = args.output_dir.resolve()
output_root.mkdir(parents=True, exist_ok=False)
roots = dict(package=package, archive=archive, emission=emission_root, d_prefix=d_prefix_root)
started = time.process_time()
pins = {}

def pin(path):
    path = Path(path)
    raw = path.read_bytes()
    entry = dict(path=str(path), bytes=len(raw), sha256=hashlib.sha256(raw).hexdigest())
    if str(path) in pins:
        assert pins[str(path)] == entry, ('input drift', path)
    pins[str(path)] = entry
    return raw

def read_json(path):
    def unique(items):
        d = {}
        for k, v in items:
            assert k not in d, ('duplicate JSON key', k)
            d[k] = v
        return d
    return json.loads(pin(path), object_pairs_hook=unique)

def safe_relative(root, relative):
    rel = Path(relative)
    assert not rel.is_absolute() and '..' not in rel.parts, ('unsafe relative path', relative)
    path = root/rel
    assert path.is_file(), ('missing indexed file', path)
    return path

index = read_json(package/'path_index.json')
assert index['schema']=='ramsey61-common-portable-path-index-v1'

def original_record(name):
    entry = index['records'][name]
    path = safe_relative(package,entry['path'])
    result = read_json(path)
    assert pins[str(path)]['sha256']==entry['sha256'], ('record hash',name)
    return result

def relocated(historical):
    entry = index['historical_paths'][historical]
    path = safe_relative(roots[entry['root']],entry['path'])
    return path

def indexed_pin(historical):
    path = relocated(historical)
    raw = pin(path)
    assert pins[str(path)]['sha256']==index['historical_paths'][historical]['sha256'], ('indexed hash',historical)
    return raw

native_order = original_record('PAIR_ADMISSION_GENERATED_001')
common_original = original_record('COMMON_NATIVE_ALL_INPUT_BINDING_001')
assert common_original['status']=='PASS_ALL_55016_COMMON_NATIVE_INPUTS'
sources = {}
for fam, entry in zip(['A', 'B', 'D'], native_order['source_pins'][:3]):
    path = relocated(entry['path'])
    indexed_pin(entry['path'])
    sources[fam] = read_json(path)
    assert pins[str(path)]['sha256']==entry['sha256']
ab_binding = original_record('ALL20_EXACT_PREFIX_BINDING_001')
d_binding = original_record('D_NATIVE_PREFIX_ALL_BINDING_001')
assert ab_binding['status'] == 'PASS' and ab_binding['count'] == 20
assert d_binding['status'] == 'PASS_ALL_TWELVE_NATIVE_D_BASE_BODIES'
body_paths = {(r['key'].split('_')[0],r['key'].split('_')[1],int(r['key'].split('_')[2])):
              (r['generated'],r['body_sha256']) for r in ab_binding['rows']}
for row in d_binding['rows']:
    if row['kind'] in ['UTU','UTT','TTU','TTT']:
        body_paths['D',row['kind'],4 if row['shape']=='four' else 5] = \
            row['emitted']['path'],row['emitted']['sha256']
body_cache = {}
for key,(path,sha) in body_paths.items():
    raw = indexed_pin(path)
    assert hashlib.sha256(raw).hexdigest() == sha
    body_cache[key] = raw

manifest_cases, prefix_states, manifests = {}, {}, {}
for fam, group in [('A','A'),('B','B')]+[('D',k) for k in ['UTU','UTT','TTU','TTT']]:
    manifest_old = index['manifests'][group]
    indexed_pin(manifest_old)
    manifest_path = relocated(manifest_old)
    directory = manifest_path.parent
    manifest = read_json(manifest_path)
    manifests[fam,group] = manifest
    for pk,entry in manifest['prefixes'].items():
        owner = pk.split('/')[0][2:] if fam!='D' else group
        stage = pk.split('/')[-1]
        free = 4 if stage.startswith('P15') else 5
        body = body_cache[fam,owner,free]
        assert hashlib.sha256(body).hexdigest() == entry['body_sha256']
        header = bytes.fromhex(entry['header_hex'])
        raw = header+body
        assert hashlib.sha256(raw).hexdigest() == entry['sha256']
        assert len(raw) == entry['bytes']
        assert body.count(b'\n') == entry['base_clauses']
        assert header.decode().split() == ['p','cnf',str(entry['variables']),str(entry['clauses'])]
        original = relocated(entry['path'])
        assert indexed_pin(entry['path']) == raw
        prefix_states[fam,group,pk] = (hashlib.sha256(raw),len(raw),entry)
    for case in manifest['cases']:
        owner = case.get('owner', group)
        key = (fam,owner,case['stage'],case['pair_index'],case['rep_index'])
        assert key not in manifest_cases
        manifest_cases[key] = (case,group)
assert len(manifest_cases) == 55016

emission_path = relocated(index['suffix_original_path'])
emission = indexed_pin(index['suffix_original_path']).decode('ascii').splitlines()
metadata, admitted, leaves = {}, collections.defaultdict(list), {}
for line in emission:
    fields = line.split('\t')
    kind,p = fields[0],int(fields[1])
    assert 0 <= p < 737
    if kind=='PAIR':
        assert p not in metadata and len(fields)==7
        metadata[p] = (fields[2], *map(int,fields[3:]))
    elif kind=='ADMIT':
        assert len(fields)==6
        entry = (fields[2],fields[3],int(fields[4]),int(fields[5]))
        assert entry not in admitted[p]
        admitted[p].append(entry)
    elif kind=='LEAF':
        assert len(fields)==5
        j,word = int(fields[2]),int(fields[3])
        assert (p,j) not in leaves
        leaves[p,j] = (word, list(map(int,fields[4].split(','))))
    else:
        raise AssertionError(('unknown row',fields))
assert set(metadata)==set(admitted)==set(range(737))

mapping_path = output_root/'COMMON_NATIVE_CASE_MAP.tsv'
mapping = mapping_path.open('x',encoding='ascii')
mapping.write('profile\towner\tfree\tpair737\trepresentative\tcase_id\tformula_sha256\tsuffix_sha256\n')
seen, count = set(),collections.Counter()
unique_leaf_count = 0
for p in range(737):
    fam,kind,stage,idx = native_order['retained_source_order'][p]
    records = sources[fam]['groups'][kind]['stages'][stage]['cases']
    records = [r for r in records if r['index']==idx]
    assert len(records)==1
    record = records[0]
    free = 4 if stage=='0' else 5
    lk = (2 if fam=='A' else 0)+(kind[0]=='T')
    rk = (2 if fam in ['A','B'] else 0)+(kind[1]=='T')
    assert metadata[p] == (fam,lk,rk,3 if stage=='None' else int(stage),len(record['reps']))
    expected_owners = {'A':['UUU','UUT','UTT','TTT'],
                       'B':['UUU','UUT','UTT','TUU','TUT','TTT'],
                       'D':['UTU','UTT','TTU','TTT']}[fam]
    expected_admits = {(fam,owner,free,len(record['reps'])) for owner in expected_owners if owner[:2]==kind}
    assert set(admitted[p]) == expected_admits
    assert set(j for pp,j in leaves if pp==p) == set(range(len(record['reps'])))
    for j,native_word in enumerate(record['reps']):
        word,units = leaves[p,j]
        word_bytes = bytes.fromhex(native_word)
        assert word == sum(c << (2*i) for i,c in enumerate(word_bytes)), ('matrix word',p,j)
        suffix = ''.join(f'{u} 0\n' for u in units).encode('ascii')
        suffix_sha = hashlib.sha256(suffix).hexdigest()
        unique_leaf_count += 1
        for _,owner,_,_ in admitted[p]:
            key = (fam,owner,stage,idx,j)
            assert key in manifest_cases and key not in seen, ('case key',key)
            seen.add(key)
            case,group = manifest_cases[key]
            assert units == case['dense_units'], ('literal mismatch',key)
            assert suffix_sha == case['suffix_sha256']
            assert hashlib.sha256(word_bytes).hexdigest() == case['matrix_word_sha256']
            state,length,prefix = prefix_states[fam,group,case['prefix_key']]
            assert len(units)+prefix['base_clauses'] == case['clauses'] == prefix['clauses']
            assert case['variables']==prefix['variables'] and max(map(abs,units))<=case['variables']
            assert length+len(suffix)==case['cnf_bytes']
            final = state.copy(); final.update(suffix)
            assert final.hexdigest()==case['cnf_sha256'], ('complete formula hash',key)
            count[fam,owner,free]+=1
            mapping.write(f"{fam}\t{owner}\t{free}\t{p}\t{j}\t{case['case_id']}\t{case['cnf_sha256']}\t{suffix_sha}\n")
assert seen == set(manifest_cases)
assert unique_leaf_count==len(leaves)
mapping.close()
pin(mapping_path)
pin(package/'Emit.lean')
pin(package/'lean/PricingABD/CommonSuffixCache.lean')
pin(Path(__file__))
result = dict(status='PASS_ALL_55016_COMMON_NATIVE_INPUTS',
    UTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),CPU_seconds=time.process_time()-started,
    retained_pairs=737,abstract_suffixes=unique_leaf_count,complete_native_inputs=len(seen),
    prefix_body_count=len(body_paths),archived_prefix_variants=len(prefix_states),
    profile_counts=dict(collections.Counter({f:sum(v for (ff,o,s),v in count.items() if ff==f) for f in ['A','B','D']})),
    profile_owner_free_counts=[dict(profile=f,owner=o,free=s,leaves=n)for(f,o,s),n in sorted(count.items())],
    checks=['Every emitted Admitted owner exactly equals the frozen original native owner domain.',
      'All737 native retained pair identities and ordered representative words match the pinned original censuses.',
      'Every ordered signed suffix literal equals the original manifest dense_units, including all91 D/free4 positive units.',
      'All20 A/B and8 mixedD mathematical prefix bodies are reused with their original headers and exact bytes.',
      'Every complete reconstructed formula SHA256, byte count, variable count and clause count equals the original frozen manifest.',
      'The mapping is bijective:55016 original case IDs, no missing cases, orphans, duplicate mappings or unadmitted additions.'],
    portable_path_index=pins[str(package/'path_index.json')],
    immutable_parent_record_hashes={name:entry['sha256']for name,entry in index['records'].items()},
    scope='A/B and mixedD UTU/UTT/TTU/TTT only. UUU/UUT679 and finalC456 are separate families. No SAT result or certificate is produced here.',
    mapping=str(mapping_path),pins=list(pins.values()),new_solver_calls=0)
output=output_root/'COMMON_NATIVE_ALL_INPUT_BINDING.json'
output.open('x').write(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ['pins','profile_owner_free_counts','checks']},indent=2))
