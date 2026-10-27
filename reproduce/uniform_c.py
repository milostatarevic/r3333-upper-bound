"""Direct marked-neighborhood units for the 346 profile-C entrance cases.

The two sixteen-vertex root cells carry U/T templates. The fourteen-vertex
cell containing the mark has no prescribed template. Its exact marked
neighborhood is fixed by positive and negative membership units.
"""
from collections import Counter
from hashlib import sha256
from itertools import combinations
import json
from pathlib import Path

SHAPES = ((4, 5, 5), (5, 4, 5), (5, 5, 4), (5, 5, 5))
FOREIGN = ('UU', 'UT', 'TT')
DATA = Path(__file__).with_name('data') / 'c_entrances.json'


def need(condition, message):
    if not condition:
        raise ValueError(message)


def validate(case):
    fields = {'case_id', 'foreign', 'shape', 'pair_index', 'rep_index',
              'left_support', 'right_support', 'word'}
    need(isinstance(case, dict) and set(case) == fields, 'C case fields')
    shape, foreign = case['shape'], case['foreign']
    need(isinstance(shape, list) and all(type(x) is int for x in shape)
         and tuple(shape) in SHAPES and foreign in FOREIGN, 'C case shape or templates')
    need(all(type(case[key]) is int and case[key] >= 0 for key in ('pair_index', 'rep_index')),
         'C pair/representative index')
    expected_id = f'{foreign}/{"".join(map(str, shape))}/pair_{case["pair_index"]:03d}/rep_{case["rep_index"]:03d}'
    need(case['case_id'] == expected_id, 'C case identifier')
    k, s, t = shape
    for key, size in (('left_support', s), ('right_support', t)):
        support = case[key]
        need(isinstance(support, list) and len(support) == size
             and all(type(v) is int and 0 <= v < 16 for v in support)
             and support == sorted(set(support)), 'C support labels')
    groups = [list(range(k)), [k+v for v in case['left_support']],
              [k+16+v for v in case['right_support']]]
    pairs = {(a, b) for i, first in enumerate(groups) for second in groups[i+1:]
             for a in first for b in second}
    word = case['word']
    need(isinstance(word, list) and all(isinstance(row, list) and len(row) == 3
         and all(type(x) is int for x in row) and 0 <= row[2] < 3 for row in word),
         'C cross-word entries')
    need(len(word) == len(pairs) and {(a, b) for a, b, _ in word} == pairs,
         'C cross-word coverage')


def load(path=DATA):
    raw = Path(path).read_bytes()
    data = json.loads(raw)
    need(isinstance(data, dict) and set(data) == {'schema', 'cases'}
         and data['schema'] == 'C_ENTRANCE_BOUNDARY_1', 'C boundary schema')
    rows = data['cases']
    need(isinstance(rows, list) and len(rows) == 346, 'C boundary cardinality')
    for case in rows:
        validate(case)
    keys = [(FOREIGN.index(r['foreign']), SHAPES.index(tuple(r['shape'])),
             r['pair_index'], r['rep_index']) for r in rows]
    need(keys == sorted(set(keys)), 'C case order or duplicate')
    need(Counter(r['foreign'] for r in rows) == {'UU': 14, 'UT': 56, 'TT': 276},
         'C template census')
    need(Counter(tuple(r['shape']) for r in rows) == dict(zip(SHAPES, (96, 112, 116, 22))),
         'C support-shape census')
    return data, {'path': 'reproduce/data/c_entrances.json', 'bytes': len(raw),
                  'sha256': sha256(raw).hexdigest()}


def units(case, edge, template):
    """Return ordered physical units; share the caller's numbering/templates."""
    validate(case)
    k = case['shape'][0]
    groups = [range(1, 15), range(15, 31), range(31, 47), range(47, 61)]
    out = [edge(61, 0, v, q) for q, group in enumerate(groups) for v in group]
    for q in (1, 2):
        palette = [color for color in range(4) if color != q]
        out.extend(edge(61, groups[q][a], groups[q][b],
                        palette[template(case['foreign'][q-1], a, b)])
                   for a, b in combinations(range(16), 2))
    out.extend(edge(61, a+1, b+1,
                    1 if b == a+1 or (k == 5 and a == 0 and b == 4) else 2)
               for a, b in combinations(range(k), 2))

    def label(v):
        return v+1 if v < k else v+15-k

    out.extend(edge(61, label(a), label(b), q) for a, b, q in case['word'])
    support = {*range(1, k+1), *(15+v for v in case['left_support']),
               *(31+v for v in case['right_support'])}
    out.extend(edge(61, 60, v, 3)*(1 if v in support else -1) for v in range(1, 60))
    expected = 430 if k == 4 else 444 if sum(case['shape']) == 15 else 434
    need(len(out) == expected and len(set(out)) == len(out)
         and not (set(out) & {-v for v in out}), 'C unit census or conflict')
    return out
