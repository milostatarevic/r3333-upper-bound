"""Balanced K61: actual-neighborhood template embeddings.

Auxiliary ranges are disjoint: 7321..7832 for five-subset selectors,
and 7833..13656 for local embeddings.
Every occurrence of a physical edge uses the common K61 numbering.
"""
from collections import Counter
from functools import lru_cache
from itertools import combinations, permutations
import json
from pathlib import Path

DATA = Path(__file__).with_name('data') / 'balance_anchors.json'
OWNERS = ('UU', 'UT', 'TT')
VARIABLES, CLAUSES = 13656, 524462


def need(condition, message):
    if not condition:
        raise ValueError(message)


@lru_cache(maxsize=None)
def tables(template):
    data = json.loads(DATA.read_text())
    need(set(data) == {'schema', 'reference', 'states', 'coverage'}
         and data['schema'] == 'BALANCE_ANCHORS_1', 'Balance anchor schema')
    matrices = {kind: [[-1 if a == b else template(kind, a, b) for b in range(16)]
                      for a in range(16)] for kind in ('U', 'T')}
    states = []
    for entry in data['states']:
        need(set(entry) == {'kind', 'order'} and entry['kind'] in matrices
             and len(entry['order']) == 16 and all(type(v) is int for v in entry['order'])
             and sorted(entry['order']) == list(range(16)), 'Balance state permutation')
        matrix = matrices[entry['kind']]
        state = [[matrix[a][b] for b in entry['order']] for a in entry['order']]
        need([row[:5] for row in state[:5]] == data['reference'], 'Balance state anchor')
        states.append(state)
    need(len(states) == 6 and Counter(r['kind'] for r in data['states']) == {'U': 1, 'T': 5},
         'Balance state boundary')
    patterns = {kind: [list(vertices) for vertices in combinations(range(16), 5)
                      if all(matrix[a][b] != 0 for a, b in combinations(vertices, 2))]
                for kind, matrix in matrices.items()}
    expected = set()
    for kind, groups in patterns.items():
        need(len(groups) == 16, 'Independent-five boundary')
        for group in groups:
            for order in permutations(group):
                if all(matrices[kind][order[a]][order[b]] == data['reference'][a][b]
                       for a, b in combinations(range(5), 2)):
                    expected.add((kind, order))
    seen = set()
    for entry in data['coverage']:
        need(set(entry) == {'kind', 'anchor', 'state', 'position_to_vertex'}, 'Anchor witness fields')
        kind, state, order = entry['kind'], entry['state'], entry['position_to_vertex']
        need(kind in matrices and type(state) is int and 0 <= state < 6
             and len(order) == 16 and all(type(v) is int for v in order)
             and sorted(order) == list(range(16)), 'Anchor witness permutation')
        need(entry['anchor'] == order[:5]
             and all(matrices[kind][order[a]][order[b]] == states[state][a][b]
                     for a, b in combinations(range(16), 2)), 'Anchor witness color preservation')
        key = kind, tuple(entry['anchor'])
        need(key not in seen, 'Duplicate ordered anchor')
        seen.add(key)
    need(len(seen) == 320 and seen == expected, 'Incomplete ordered-anchor coverage')
    return matrices, states, patterns, data['reference']


def root_color(v):
    need(1 <= v <= 60, 'Nonroot vertex expected')
    return 0 if v <= 16 else 1 if v <= 32 else 2 if v <= 46 else 3


def scope(owner, side, center, matrices, reference):
    own = matrices[owner[side]]
    anchor_set = [v for v in range(16) if own[center][v] == 0]
    orders = [order for order in permutations(anchor_set)
              if all(own[order[a]][order[b]] == reference[a][b]
                     for a, b in combinations(range(5), 2))]
    need(len(anchor_set) == 5 and orders, 'Physical anchor ordering')
    return min(orders), 7833 + 182*(16*side+center)


def embedding_clauses(owner, side, center, edge, matrices, states, reference):
    anchor, first = scope(owner, side, center, matrices, reference)
    state_bits = tuple(first+176+s for s in range(6))
    role = lambda member, label: first+11*member+label
    own_start, other_start = (1, 17) if side == 0 else (17, 1)
    scope_color = 1-side
    active = lambda member: edge(61, own_start+center, other_start+member, scope_color)
    palette = tuple(q for q in range(4) if q != scope_color)
    yield state_bits
    yield from ((-a, -b) for a, b in combinations(state_bits, 2))
    for m in range(16):
        roles = tuple(role(m, t) for t in range(11))
        yield (-active(m),) + roles
        yield from ((-variable, active(m)) for variable in roles)
        yield from ((-a, -b) for a, b in combinations(roles, 2))
    for a, b in combinations(range(16), 2):
        for label in range(11):
            yield (-role(a, label), -role(b, label))
    for m in range(16):
        for label in range(11):
            for a in range(5):
                colors = [palette[matrix[a][5+label]] for matrix in states]
                choices = sorted(set(colors))
                physical = lambda q: edge(61, own_start+anchor[a], other_start+m, q)
                if len(choices) == 1:
                    yield (-role(m, label), physical(choices[0]))
                else:
                    for q in palette:
                        if q not in choices:
                            yield (-role(m, label), -physical(q))
                    for state, q in enumerate(colors):
                        yield (-role(m, label), -state_bits[state], physical(q))
    other = matrices[owner[1-side]]
    for a, b in combinations(range(16), 2):
        color = other[a][b]
        for label in range(11):
            supports = [tuple(t for t in range(11) if t != label and matrix[5+label][5+t] == color)
                        for matrix in states]
            if len(set(supports)) == 1:
                yield (-role(a, label), -active(b)) + tuple(role(b, t) for t in supports[0])
            else:
                for state, support in enumerate(supports):
                    yield (-role(a, label), -state_bits[state], -active(b)) + tuple(role(b, t) for t in support)


def extra_clauses(owner, edge, template):
    """Append to the shared good-coloring base, preserving the declared order."""
    need(owner in OWNERS, 'Balanced owner')
    matrices, states, patterns, reference = tables(template)
    for v in range(1, 61):
        yield (edge(61, 0, v, root_color(v)),)
    for side, start in enumerate((1, 17)):
        palette = (1, 2, 3) if side == 0 else (0, 2, 3)
        for a, b in combinations(range(16), 2):
            yield (edge(61, start+a, start+b, palette[matrices[owner[side]][a][b]]),)
    for x in range(16):
        for y in range(16):
            values = tuple(edge(61, 1+x, 17+y, q) for q in range(4))
            yield values
            yield from ((-a, -b) for a, b in combinations(values, 2))
    for a, b in combinations(range(16), 2):
        for v in range(16):
            xc = (1, 2, 3)[matrices[owner[0]][a][b]]
            yc = (0, 2, 3)[matrices[owner[1]][a][b]]
            yield (-edge(61, 1+a, 17+v, xc), -edge(61, 1+b, 17+v, xc))
            yield (-edge(61, 1+v, 17+a, yc), -edge(61, 1+v, 17+b, yc))
    for number in range(32):
        side, center = divmod(number, 16)
        pattern = lambda index: 7321+16*number+index
        values = tuple(pattern(index) for index in range(16))
        yield values
        yield from ((-a, -b) for a, b in combinations(values, 2))
        for index, vertices in enumerate(patterns[owner[1-side]]):
            for member in range(16):
                literal = (edge(61, center+1, member+17, 0) if side == 0 else
                           edge(61, member+1, center+17, 1))
                yield (-pattern(index), literal if member in vertices else -literal)
    for side in range(2):
        for center in range(16):
            yield from embedding_clauses(owner, side, center, edge, matrices, states, reference)
