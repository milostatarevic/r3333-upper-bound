#!/usr/bin/env python3
"""One K61 edge-coloring CNF: shared exactly-one/triangle base, then case units.

Authenticated manifests and finite support/word tables supply case data, not
clauses or solver answers. No campaign generator is imported.
"""
import argparse
from collections import Counter
from functools import lru_cache
import gzip
import hashlib
from itertools import combinations
import json
import math
from pathlib import Path
import tarfile
import uniform_c
import uniform_balance

ARCHIVE_SHA = '2b85cac94df0317a532aa823cfea93ac83738093fc854805896943f90d468757'
BASE_SHA = 'f974e4a1e44ae758ba748fc91838cd820cfb807ed4c09e7ffa5dc661d267565e'
VARIABLES, BASE_CLAUSES = 7320, 156770
COUNTS = {'A': 360, 'B': 5096, 'D_UUU': 679, 'D_UUT': 679,
          'D_UTU': 6576, 'D_UTT': 6576, 'D_TTU': 18204, 'D_TTT': 18204,
          'C': 346, 'BALANCE': 3}
SOURCES = {
    'A': 'evidence/A/full_inputs_000/MANIFEST.json',
    'B': 'evidence/B/full_inputs_000/MANIFEST.json',
    **{f'D_{s}': f'evidence/D/mixed/full_inputs_{s}_000/MANIFEST.json'
       for s in ('UTU', 'UTT', 'TTU', 'TTT')},
}


def need(ok, message):
    if not ok:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def file_pin(path):
    h, size = hashlib.sha256(), 0
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1 << 20), b''):
            h.update(block)
            size += len(block)
    return {'sha256': h.hexdigest(), 'bytes': size}


def line(clause):
    return (' '.join(map(str, clause)) + ' 0\n').encode('ascii')


def edge(n, a, b, color):
    a, b = sorted((a, b))
    need(0 <= a < b < n and 0 <= color < 4, 'Invalid physical edge')
    return 4 * (a * (2*n-a-1)//2 + b-a-1) + color + 1


@lru_cache(maxsize=None)
def edge_table(n):
    return [(a, b, q) for a, b in combinations(range(n), 2) for q in range(4)]


def decode(literal, n):
    need(0 < abs(literal) <= 4*math.comb(n, 2), 'Non-edge case literal')
    return edge_table(n)[abs(literal)-1]


@lru_cache(maxsize=1)
def base():
    clauses = []
    for a, b in combinations(range(61), 2):
        row = [edge(61, a, b, q) for q in range(4)]
        clauses.append(line(row))
        clauses.extend(line((-x, -y)) for x, y in combinations(row, 2))
    for a, b, c in combinations(range(61), 3):
        clauses.extend(line((-edge(61, a, b, q), -edge(61, a, c, q),
                             -edge(61, b, c, q))) for q in range(4))
    body = b''.join(clauses)
    need(len(clauses) == BASE_CLAUSES and sha(body) == BASE_SHA, 'Base mismatch')
    return body


def template(kind, a, b):
    directions = ({1, 8, 10, 12, 15}, {2, 3, 7, 11, 13}, {4, 5, 6, 9, 14})
    q = next(i for i, group in enumerate(directions) if a ^ b in group)
    left, right = {1, 2, 8, 11}, {5, 6, 12, 15}
    if kind == 'T' and ((a in left and b in right) or (b in left and a in right)):
        need(q in (1, 2), 'Invalid template switch')
        q = 3-q
    need(kind in ('U', 'T'), 'Invalid template kind')
    return q


def blocks(orders):
    out, start = [], 1
    for size in orders:
        out.append(list(range(start, start+size)))
        start += size
    need(start == 61, 'Root cells do not partition 60 vertices')
    return out


def spokes(groups):
    return [edge(61, 0, v, q) for q, vertices in enumerate(groups) for v in vertices]


def critical_units(groups, owner):
    units = []
    for q in (1, 2, 3):
        palette = [c for c in range(4) if c != q]
        units.extend(edge(61, groups[q][a], groups[q][b], palette[template(owner[q-1], a, b)])
                     for a, b in combinations(range(len(groups[q])), 2))
    return units


def ordered_unique(units):
    out = list(dict.fromkeys(units))
    need(not (set(out) & {-u for u in out}), 'Conflicting case units')
    return out


def ab_units(family, manifest, case):
    pin = manifest['prefixes'][case['prefix_key']]
    k, n = pin['free_size'], pin['vertices']
    groups = blocks([12, 16, 16, 16] if family == 'A' else [13, 15, 16, 16])
    old = pin['block_vertices']
    need([len(g) for g in old] == [k]+[len(g) for g in groups[1:]], 'A/B block dimensions')
    mapping = {v: groups[q][i] for q, group in enumerate(old) for i, v in enumerate(group)}
    mark = n-1
    need(mapping[mark] == 60, 'Mark label mismatch')
    length = len(old[1])+len(old[2])
    membership, word = case['dense_units'][:length], case['dense_units'][length:]
    support = {0, *groups[0][:k]}
    for v, lit in zip(old[1]+old[2], membership):
        need(abs(lit) == edge(n, v, mark, 3), 'A/B membership mismatch')
        if lit > 0:
            support.add(mapping[v])
    units = spokes(groups)+critical_units(groups, case['owner'])
    units += [edge(61, groups[0][a], groups[0][b],
                   1 if b == a+1 or (k == 5 and a == 0 and b == 4) else 2)
              for a, b in combinations(range(k), 2)]
    for lit in word:
        a, b, q = decode(lit, n)
        need(lit > 0 and q < 3, 'Invalid cross word')
        units.append(edge(61, mapping[a], mapping[b], q))
    units += [edge(61, 60, v, 3)*(1 if v in support else -1) for v in range(60)]
    return ordered_unique(units)


def d_source_facts(case):
    """Normalize a finite source record to physical K61 facts at input loading."""
    k = 4 if case['prefix_key'] == 'P15_MATRIX_ONLY' else 5
    n = k+46
    def label(a):
        return a+1 if a < k else a+15-k
    shapes, cross, inside, membership = {}, {}, {}, {}
    for lit in case['dense_units']:
        a, b, q = decode(lit, n)
        need(0 <= a < b < n and 0 <= q < 4, 'Invalid D source edge')
        if b == n-1 and q == 3:
            membership[a] = lit > 0
        elif lit > 0 and b < k:
            shapes[a, b] = q
        elif lit > 0 and (k <= a < b < k+15 or k+15 <= a < b < k+30):
            inside[a, b] = q
        else:
            need(lit > 0 and q < 3, 'Invalid D source word')
            cross[a, b] = q
    if k == 4:
        need(len(shapes) == 6 and len(inside) == 20 and not membership, 'D source structure')
        selected = {v for pair in inside for v in pair}
    else:
        need(set(membership) == set(range(k, k+30)), 'D source membership missing')
        selected = {v for v, yes in membership.items() if yes}
        shapes = {(a, b): 1 if b-a in (1, 4) else 2 for a, b in combinations(range(k), 2)}
    return {'case_id': case['case_id'], 'free_size': k,
            'support': sorted({*range(1, k+1), *(label(v) for v in selected)}),
            'free_edges': [[label(a), label(b), q] for (a,b),q in sorted(shapes.items())],
            'cross_edges': [[label(a), label(b), q] for (a,b),q in sorted(cross.items())]}


def d_units(owner, case):
    """The same physical fact constructor for every D owner."""
    k, support = case['free_size'], case['support']
    need(k in (4,5) and support == sorted(set(support)), 'Invalid D support')
    left = [v for v in support if 15 <= v < 30]
    right = [v for v in support if 30 <= v < 45]
    need(support == list(range(1,k+1))+left+right
         and len(left) in (4,5) and len(right) in (4,5)
         and len(support) in (14,15), 'Invalid D support shape')
    free_edges, cross_edges = case['free_edges'], case['cross_edges']
    expected_cross = [(a,b) for a in range(1,k+1) for b in left+right]
    expected_cross += [(a,b) for a in left for b in right]
    need([tuple(e[:2]) for e in free_edges] == list(combinations(range(1,k+1),2))
         and all(e[2] in (1,2) for e in free_edges), 'Invalid free-support facts')
    need([tuple(e[:2]) for e in cross_edges] == expected_cross
         and all(e[2] in range(3) for e in cross_edges), 'Invalid cross-support facts')
    groups = blocks([14,15,15,16])
    units = spokes(groups)+critical_units(groups,owner)
    units += [edge(61,*fact) for fact in free_edges+cross_edges]
    units += [edge(61,60,v,3)*(1 if v in support else -1) for v in range(1,60)]
    need(len(set(units)) == len(units), 'Repeated D unit')
    return ordered_unique(units)


MARKED_UU_DATA = Path(__file__).with_name('data')/'marked_uu.json'
MARKED_UU_SHA = '83718289fe149a28e26daf9a5f96dea4f806b06352fec3c89de29738681689b1'


def load_marked_uu():
    raw = MARKED_UU_DATA.read_bytes()
    need(sha(raw) == MARKED_UU_SHA, 'Marked U/U finite-data identity')
    data = json.loads(raw)
    need(data['schema'] == 'UNIFORM_K61_MARKED_UU_DATA_1', 'Marked U/U data schema')
    rows = data['cases']
    need(len(rows) == 679 and sorted(row['index'] for row in rows) == list(range(679))
         and len({row['case_id'] for row in rows}) == 679, 'Marked U/U finite census')
    return data, {'path':'reproduce/data/marked_uu.json','bytes':len(raw),'sha256':sha(raw)}


def c_units(case):
    return uniform_c.units(case, edge, template)


def load_sources(archive):
    need(file_pin(archive)['sha256'] == ARCHIVE_SHA, 'Unauthenticated v1 archive')
    wanted = {v: k for k, v in SOURCES.items()}
    found, pins = {}, {}
    with tarfile.open(archive, mode='r|gz') as stream:
        for member in stream:
            if member.name not in wanted:
                continue
            key = wanted[member.name]
            need(key not in found and member.isfile() and not member.issparse()
                 and member.size <= 64 << 20, 'Invalid case-data archive member')
            raw = stream.extractfile(member).read()
            need(len(raw) == member.size, 'Truncated case data')
            found[key] = json.loads(raw)
            pins[key] = {'path': member.name, 'bytes': len(raw), 'sha256': sha(raw)}
    need(set(found) == set(SOURCES), 'Missing case data')
    for family in ('D_UTU','D_UTT','D_TTU','D_TTT'):
        found[family] = {'cases': [d_source_facts(row) for row in found[family]['cases']]}
    found['D_UU'], pins['D_UU'] = load_marked_uu()
    found['C'], pins['C'] = uniform_c.load()
    found['BALANCE'] = {'cases': [{'case_id': owner} for owner in uniform_balance.OWNERS]}
    pins['BALANCE'] = {'path': 'reproduce/data/balance_anchors.json',
                       **file_pin(uniform_balance.DATA)}
    return found, pins


def cases(sources, families=None):
    selected = set(COUNTS if families is None else families)
    need(selected and selected <= COUNTS.keys(), 'Unknown or empty family selection')
    seen, counts = set(), Counter()
    for family in COUNTS:
        data = sources['D_UU' if family in ('D_UUU', 'D_UUT') else family]
        rows = data['cases']
        for case in rows:
            cid = case['case_id']
            need((family, cid) not in seen, 'Duplicate case')
            seen.add((family, cid)); counts[family] += 1
            if family not in selected:
                continue
            if family == 'BALANCE':
                yield {'id': len(seen)-1, 'family': family, 'case_id': cid,
                       'file': f'balanced/{cid}.cnf'}
                continue
            units = (ab_units(family, data, case) if family in ('A', 'B') else
                     c_units(case) if family == 'C' else d_units(family[2:], case))
            need(all(0 < abs(x) <= VARIABLES for x in units), 'Invalid unit variable')
            need(not (set(units) & {-x for x in units}), 'Conflicting units')
            yield {'id': len(seen)-1, 'family': family, 'case_id': cid, 'units': units}
    need(dict(counts) == COUNTS, 'Incomplete finite boundary')


@lru_cache(maxsize=None)
def prefix(unit_count):
    data = f'p cnf {VARIABLES} {BASE_CLAUSES+unit_count}\n'.encode()+base()
    return data, hashlib.sha256(data)


@lru_cache(maxsize=3)
def balance_formula(owner):
    first = f'p cnf {uniform_balance.VARIABLES} {uniform_balance.CLAUSES}\n'.encode() + base()
    tail = b''.join(line(clause) for clause in uniform_balance.extra_clauses(owner, edge, template))
    need(tail.count(b'\n') == uniform_balance.CLAUSES-BASE_CLAUSES, 'Balanced clause census')
    return (first, tail), {'sha256': sha(first+tail), 'bytes': len(first)+len(tail),
                          'variables': uniform_balance.VARIABLES, 'clauses': uniform_balance.CLAUSES}


def formula(row):
    if row['family'] == 'BALANCE':
        return balance_formula(row['case_id'])
    first, state = prefix(len(row['units']))
    tail = b''.join(line((u,)) for u in row['units'])
    h = state.copy(); h.update(tail)
    return (first, tail), {'sha256': h.hexdigest(), 'bytes': len(first)+len(tail),
                          'variables': VARIABLES, 'clauses': BASE_CLAUSES+len(row['units'])}


def prepare(archive, output, families=None):
    selected = [family for family in COUNTS if families is None or family in families]
    need(selected and (families is None or set(selected) == set(families)), 'Unknown family selection')
    output.mkdir(parents=True, exist_ok=False)
    sources, pins = load_sources(archive)
    (output/'base.clauses').write_bytes(base())
    count = 0
    with (output/'cases.jsonl.gz').open('xb') as raw:
        with gzip.GzipFile(filename='', mode='wb', fileobj=raw, mtime=0) as stream:
            for row in cases(sources, selected):
                if families is not None:
                    row['current_index'], row['id'] = row['id'], count
                pieces, row['formula'] = formula(row)
                if row['family'] == 'BALANCE':
                    target = output/row['file']
                    target.parent.mkdir(exist_ok=True)
                    with target.open('xb') as file:
                        for piece in pieces:
                            file.write(piece)
                stream.write((json.dumps(row, separators=(',', ':'))+'\n').encode())
                count += 1
    manifest = {'schema': 'UNIFORM_K61_INPUTS_2', 'cases': count,
                'family_counts': {family: COUNTS[family] for family in selected},
                'complete_family_counts': COUNTS,
                'source_archive_sha256': ARCHIVE_SHA, 'sources': pins,
                'base': file_pin(output/'base.clauses'),
                'catalog': file_pin(output/'cases.jsonl.gz'),
                'generator': file_pin(__file__),
                'generator_dependencies': {'uniform_c.py': file_pin(uniform_c.__file__),
                                           'uniform_balance.py': file_pin(uniform_balance.__file__)}}
    (output/'MANIFEST.json').write_text(json.dumps(manifest, indent=2)+'\n')
    return manifest


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command', choices=('prepare', 'materialize'))
    parser.add_argument('--archive', type=Path, default=Path(__file__).resolve().parents[1]/'archives/evidence-v1.tar.gz')
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--family', choices=COUNTS)
    parser.add_argument('--case')
    parser.add_argument('--families', nargs='+', choices=COUNTS,
                        help='Prepare a complete subset of families for a separate campaign')
    args = parser.parse_args()
    if args.command == 'prepare':
        print(json.dumps(prepare(args.archive, args.output, args.families), indent=2))
    else:
        need(args.family and args.case, '--family and --case required')
        sources, _ = load_sources(args.archive)
        found = [r for r in cases(sources, [args.family])
                 if (r['family'], r['case_id']) == (args.family, args.case)]
        need(len(found) == 1, 'Unknown case')
        pieces, pin = formula(found[0])
        with args.output.open('xb') as stream:
            for piece in pieces:
                stream.write(piece)
        need(file_pin(args.output) == {k: pin[k] for k in ('sha256', 'bytes')}, 'Output mismatch')
        print(json.dumps(pin))


if __name__ == '__main__':
    main()
