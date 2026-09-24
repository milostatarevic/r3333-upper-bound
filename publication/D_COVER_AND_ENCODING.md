# The D cover and its exact formula semantics

This supplement supplies the mathematical and encoding details behind
[proof.md §3.3](../proof.md#33-d-the-uu-and-mixed-foreign-block-covers).
Its conclusion is an implication: every good four-coloring of K61 with a
supplied profile-D root r and H(r) ≥ 46 produces a satisfying assignment of
one formula in the listed D families. Refutation of every required formula
therefore excludes that supplied root. The argument uses one coloring
throughout, without a maximal-root hypothesis.

The [A/B/D evidence index](ABD_EVIDENCE_INDEX.md) locates the literal tables,
censuses, input manifests, reconstruction sources and native result records.
Paths beginning `evidence/`, `mathematics/` or `support/` below are relative
to the authenticated extracted evidence snapshot, as described in
[REPRODUCIBILITY.md](REPRODUCIBILITY.md). The finite tables are part of the
argument. Counts alone, and equality of reconstructed input bytes alone,
do not establish their mathematical coverage.

## 1. Extracting physical vertices from a supplied host

Write the root cells as F14, M15, X15, Q16, with root-spoke colors
0, 1, 2, 3 respectively. A good coloring has no monochromatic triangle.
Each root cell consequently omits its spoke color. Every vertex has each
full color degree between 12 and 16: the upper bound follows from the
three-color K17 bound, and the lower bound from the other three upper bounds.
An endpoint x is high on rx when its full degree in color c(rx) is at least
15; H(r) counts these endpoints.

There are only 44 nonroot vertices outside Q. Thus H(r) ≥ 46 supplies at
least two high endpoints in Q. Choose one, x. Classify the three critical
blocks using the K15/K16 classification and its literal U/T templates.
Normalize x to local coordinate 15 of Q by a color-preserving automorphism
of Q. This is a permutation of actual vertices carrying all their incident
edges. Weak catalogue palettes can be absorbed by palette-realizing vertex
maps of each template; the coloring still has a single global palette.
The classification and explicit template symmetry facts are the dependencies
specified in [CLASSIFICATION_PROVENANCE.md](CLASSIFICATION_PROVENANCE.md)
and proof.md §1.

Let S_F, S_M, S_X be x's color-3 neighbors in F, M, X. There are no further
color-3 neighbors of x inside Q. Each support omits both color 3 and its
root-cell color, so is a good two-colored clique and has at most five
vertices. The root contributes one color-3 neighbor of x. Consequently

```math
14\leq |S_F|+|S_M|+|S_X|\leq15,
```

and the exact ordered shapes are 455, 545, 554, 555. Retain every vertex of
M, X, Q and exactly the actual vertices of S_F. The resulting rootless
coloring has 50 or 51 vertices. The original root is restored only when
classifying N3(x); it is not a new host vertex.

| Shape (F,M,X) | Restored neighborhood N3(x) | Branch |
|---|---|---|
| 4,5,5 | K15 | P15 |
| 5,4,5 | K15 | D9, first foreign support short |
| 5,5,4 | K15 | D9, second foreign support short |
| 5,5,5 | K16 | D10 |

The numbers in P15/D9/D10 describe a restored neighborhood or x's foreign
color-3 degree; they are not the retained host orders. Inside N3(x), the
root's color cells are the three supports. Its five-vertex cells are
complementary colored C5s. Its four-vertex cell consists of complementary
colored P4s, because the classified K15 is a deletion from a critical K16.
This P4 conclusion uses that classification; it is not true for every good
two-colored K4.

The word UUT, for example, specifies physical M=U15, X=U15, Q=T16. It says
nothing about whether the separately classified N3(x) has restored type U
or T. Both restored types must be included for every physical owner.

## 2. What a finite support/matrix cover must check

For each ordered shape, classify N3(x) as U or T, retaining every eligible
reference root and every compatible group labeling. The three group colors
at the restored root are 0,1,2. Put each group in a fixed colored P4/C5
order. For K15 use all reference roots with the specified ordered degree
vector; for K16 vertex transitivity allows reference root 15. Reading all
cross-group edges gives 600 distinct words per shape: 100 from U and 500
from T. The canonical word orders have 65 cross edges for the deficient
shapes and 75 for 555. They are labeled matrices, not 600 isomorphism types.

For a physical foreign block, enumerate its subsets of the required size,
keep those isomorphic to the required *colored* P4/C5, and quotient by
color-preserving automorphisms of the entire K15. A support-only
isomorphism is insufficient unless it extends to that whole physical block.
The literal support counts are:

| Physical K15 | Proper five-sets | Five-set orbits | Proper four-sets | Four-set orbits | Whole-block color-preserving automorphisms |
|---|---:|---:|---:|---:|---:|
| U | 11 | 3 | 60 | 8 | 10 |
| T | 11 | 7 | 72 | 38 | 2 |

Both templates have 90 color-3-independent four-sets, so independence alone
would give the wrong four-support catalogue. For each ordered pair of
support representatives, use their extending stabilizers and the
color-preserving automorphisms of the canonical free P4/C5 to act on the
600 words. The required check is that the representative orbits cover
**every** word, with the stated physical action on every edge. These
permutations fix Q pointwise and extend over all other vertices and edges
of the host.

Canonical and physical orders must be distinguished. If an isomorphism
f sends the sorted physical support to canonical labels, canonical position
j is placed at f inverse(j), not at the jth sorted support vertex. The
mixed census records this inverse as `physical_order1/2`. Its words are
serialized by group pairs (0,1), (0,2), (1,2), then by the two canonical
indices. The original UU P15 and D10 tables use full upper-triangle words
and their own literal label numbers; their label numbers are not indices
into the canonical 600-word list. In particular, original P15 allows all
four-free-row permutations before quotienting, whereas the canonical
P4 description fixes the free inside pattern first. These are two ways
to enumerate the same physical coverage problem.

The retained construction is explicit in
`support/workspace/r4333_upper/pro_findings_review_2026_09_11/ramsey61_research/marked_catalogue.py`
and `template_math.py`. The mixed verifier
`evidence/D/mixed/tools/verify_mixed_d_boundary_000.py` independently
reconstructs the four catalogues, support sets, whole-block actions and
all ordered pair orbit covers against `direct_profile_counts.json`.
Its retained `MIXED_D_VERIFIED_CENSUS_000.json` and
`INDEPENDENT_MIXED_D_FINITE_DATA_REVIEW_000.json` record the full ordered
UT/TT check: 842 support-pair records and 505,200 pair-word incidences.
The exact locators and identities are in the evidence index.

## 3. Exchanging equal foreign blocks with one global palette

The following whole-host transformation justifies every foreign-block
exchange used here, for either Q=U16 or Q=T16. Let pi exchange colors 1 and
2, fixing 0 and 3. Exchange the entire M and X blocks at the same time.
When their types are equal, the canonical palettes [0,2,3] and [0,1,3]
transform into one another with their local coordinates unchanged.

Q's internal colors also change under the same global pi. To restore its
canonical matrix without moving its marked coordinate, choose a template
vertex permutation psi satisfying

```math
Q(\psi u,\psi v)=\pi(Q(u,v)).
```

Put b = psi inverse(15). Choose a color-preserving automorphism alpha of Q
with alpha(b)=15, and set theta = psi composed with alpha inverse. Then

```math
\theta(15)=15,\qquad Q(\theta u,\theta v)=\pi(Q(u,v)).
```

Pull back Q by theta while applying pi to the whole coloring. Since pi is
an involution, Q returns to its literal template. This calculation uses
only palette symmetry and color-preserving vertex transitivity of the
explicit U/T16, whose finite maps are retained in
`support/workspace/R4333Lean/CriticalTemplatePaletteSymmetry.lean` and
`CriticalTemplateDeletion.lean`. It does not require an embedding of the
whole U16 stabilizer into the T16 stabilizer.

If free rows have already been put in canonical order, restore that order
as well: for a path whose consecutive edges have color 1, the pullback
[2,0,3,1] identifies its complement with that path; for a cycle use
[0,2,4,1,3], equivalently i maps to 2i modulo 5. Extend this permutation
arbitrarily to the omitted vertices of F. Every cross edge, including every
Q-to-outside edge, is transported with its endpoints and recolored by the
same pi. The original root stays fixed, its root colors 0 and 3 stay fixed,
x remains the selected endpoint, and goodness, H(r), the profile and all
support cardinalities are preserved.

This gives an actual transformation of one full host. It does not replace
only selected internal template edges of a partial assignment. Ordinary
support/stabilizer maps fix Q pointwise; the exchange above is the only
step needing a palette compensation on Q. Since N3(x) contains no other
Q vertex, the induced free/foreign matrix action is independent of Q's
type. The transport records E17/E18 specify the same whole-host map.

## 4. The exact retained family counts

### Two foreign U15 blocks

The three five-support representatives have local vertex sets
[0,1,2,10,13], [0,1,3,11,12], [1,6,9,10,11], with source labels 0,1,4.
For P15, the ordered support-pair matrix-orbit counts are

```text
76 76 16
76 76 16
16 16  4
```

Their sum is 372. The explicit exchange relation in
`support/workspace/r4333_upper/profile_d_four_support_discovery/uuu_b2_p15_swap_quotient.json`
partitions these labels into 183 pairs and six fixed classes, leaving
189 representatives. The relation, rather than division of a total by
two, specifies which representative is used. The 189 actual suffixes
are in `evidence/D/UUU/census/P15_MATRIX_ONLY_189.json`.

For D9 the exchange puts the four-support in the first foreign block.
Reclassify the restored K15 after that transformation: the restored
reference-root representatives are U/root2 and T/root1, T/root4,
T/root12. Their assignment-orbit counts are 72,132,132,72, summing to 408.
The physical mark is still x at Q coordinate 15; these reference-root
numbers are not new choices of the K61 root.

For a fixed restored root, the exhaustive assignment construction takes
all ten compatible free-C5 labelings, all 11 large supports with ten
compatible labelings each, and all 60 proper small supports with two
compatible labelings each. The finite quotient uses whole-U15 maps and
any compatible restored-label symmetries. Its literal assignment
representatives and maps are retained in `d9_case_census.py`, the strong
`assignment-orbits.json` and the three `twisted_root*_orbits.json` files,
indexed alongside the four `D9_*ROOT*.json` native censuses. Thus the
408 assertion is about the complete assignment cover, including both
restored types, rather than only one apparently similar root case.

D10 keeps the foreign supports ordered. Its nine support-pair counts are
16,16,4,16,16,4,4,4,2, summing to 82; no foreign exchange is needed for this
82-case quotient. Both the discovery table and the literal
`support/workspace/R4333Lean/ProfileDDegreeTenMatrixLeafDataUUU2P15.lean`
retain the full matrix words. They join to
`evidence/D/UUU/census/D10_B2P15_82.json`.

The resulting UU cover has 189 + 408 + 82 = 679 cases. Changing Q from U
to T leaves all the finite free/foreign data valid, including the marked
exchange in §3, but changes the formula's Q-template clauses. UUU and
UUT therefore each require their own 679 exact formulas and their own
UNSAT evidence. A UUU answer is not a UUT answer.

### Mixed foreign blocks

The complete ordered table retains both deficiency orientations. For TT,
perform the exchange *before* choosing a matrix representative: if the
two five-support orbit indices satisfy i > j, exchange them and then
classify the resulting matrix in the complete catalogue for (j,i).
Keep i ≤ j and every matrix representative on each diagonal pair. For
D9 the same exchange moves the deficiency to the first foreign block.
For UT, an exchange changes the ordered physical types to TU; choose UT
as the owner frame but keep both deficiency orientations within it.

| Foreign types / retained selection | P15 | D9 first short | D9 second short | D10 | Total per Q type |
|---|---:|---:|---:|---:|---:|
| UT, all ordered pairs | 1,824 | 1,992 | 2,388 | 372 | 6,576 |
| TT, all ordered pairs | 9,084 | 11,892 | 11,892 | 1,824 | 34,692 |
| TT, selected cover | 5,256 | 11,892 | covered by exchange | 1,056 | 18,204 |

TT retains 28 of its 49 five-support pairs. The P15 diagonal contributes
1,428 words and the D10 diagonal 288, all retained. Thus 5,256 and 1,056
are not arbitrary halves of 9,084 and 1,824. The full ordered finite
check precedes this selection. The retained selection and physical
transport are specified in
`evidence/D/mixed/TT_SUPPORT_PAIR_PRECLASSIFICATION_REDUCTION_000.md`.

The six required owners are UUU, UUT, UTU, UTT, TTU, TTT with totals
679,679,6576,6576,18204,18204, respectively: 50,918 D formulas. The first
two letters specify the foreign K15s, the last Q16. The same exchange
accounts for omitted TU owner frames; it never identifies the two Q types.

## 5. Clause families and why a host satisfies them

For k retained free vertices, use positions 0 through k−1 for them,
k through k+14 for M, k+15 through k+29 for X, and k+30 through k+45 for Q.
The selected x is k+45. The original root is absent. For a < b and color q,
write E(a,b,q) for the edge-color Boolean variable. Set it true exactly
when the retained physical edge has color q.

The common good-coloring clauses are one positive four-literal clause
per edge, six pairwise color-exclusion clauses per edge, and
¬E(a,b,q) or ¬E(a,c,q) or ¬E(b,c,q) for each a<b<c and each q. They enforce
one color per edge and no monochromatic triangle. There are
7 choose(n,2) + 4 choose(n,3) such clauses. The 330 positive template units
are 105 for M, 105 for X and 120 for Q, using palettes [0,2,3], [0,1,3]
and [0,1,2]. These are necessary because the three full physical blocks
have already been classified and relabeled.

### P15: the four-row base is a deliberate relaxation

The exact four-row base has 86,975 good-coloring clauses, 330 template
units and six negative color-0 units on free/free edges, totaling 87,311.
It has **no row-degree counters and no selected-column units**. Its suffix
specifies all 91 edges of the actual 14-vertex free4/support5/support5
matrix: six free edges, 20 support-internal edges and 65 cross edges.
The final formula has 87,402 clauses.

The extracted host satisfies the omitted membership and degree conditions,
but dropping them only weakens its formula. This direction is sufficient:
a host still satisfies the weaker formula, so that formula's UNSAT answer
excludes it. UNSAT of a stronger position-specific formula would not by
itself establish UNSAT of this matrix-only formula. The actual 91-unit
census and corresponding result identities are the required evidence.

### D9/D10: five-row base and the 42 counters

The exact five-row base has the following ordered components:

| Component | Clauses |
|---|---:|
| Good coloring on 51 vertices | 92,225 |
| Three internal template blocks | 330 |
| Free/free edges forbid color 0 | 10 |
| Five free-to-x edges have color 3 | 5 |
| Canonical free C5: cycle color 1, complement color 2 | 10 |
| 42 sequential counter blocks | 250,788 |
| **Base total** | **343,368** |

All free-row bounds concern edges into the complete 46-vertex tail,
not merely the selected supports. To derive them, let a be one of the
retained vertices of F. In the original full F14, its 13 internal edges
use colors 1,2,3. Each color degree there is at most five, hence each
is at least 13−5−5=3. Writing t_q for a's tail degree and s_q for its
full-F internal degree, the actual root edge gives

```math
t_0=d_0(a)-1\in[11,15],\qquad
t_q=d_q(a)-s_q\in[7,13]\quad(q=1,2,3).
```

These bounds are derived before deleting any other F vertices. For x,
its five free color-3 neighbors and root spoke contribute six. Its
color-3 tail degree u is therefore d3(x)−6, so 9 ≤ u ≤ 10. There are no
color-3 neighbors of x in the other 15 Q vertices, making u exactly its
foreign color-3 degree.

Each of five rows and four colors has one upper and one lower counter,
giving 40 blocks. The two remaining blocks bound u. Lower bounds are
encoded as upper bounds on the *other-color edge variables*. One-hot
edge clauses make their true-input counts the required complements:

| Repeated counter | Input list | Cap | Consequence |
|---|---|---:|---|
| Each free row, q=0 | Its 46 tail edge variables of color 0 | 15 | t0 ≤ 15 |
| Each free row, q=0 | All 138 tail variables of colors other than 0 | 35 | 46−t0 ≤ 35 |
| Each free row, q≠0 | Its 46 tail edge variables of color q | 13 | tq ≤ 13 |
| Each free row, q≠0 | All 138 tail variables of colors other than q | 39 | 46−tq ≤ 39 |
| Mark x | Its 45 other-tail edge variables of color 3 | 10 | u ≤ 10 |
| Mark x | All 135 other-tail variables of colors 0,1,2 | 36 | 45−u ≤ 36 |

For a list y0,…,y(n−1) and cap b, auxiliary S(i,j) means at least j+1 of
the inputs through i are true. The actual sequential encoding emits:

- yi implies S(i,0), for every i;
- S(i,j) implies S(i+1,j), for i<n−1 and 0≤j≤b;
- yi+1 and S(i,j) imply S(i+1,j+1), for i<n−1 and 0≤j<b;
- the negative unit ¬S(n−1,b).

Whenever the cap holds, assigning each S its stated prefix-count meaning
satisfies every clause. Thus these auxiliary variables can always be
extended from the extracted physical coloring. Conversely, the forward
implications propagate any overflow to the forbidden last variable.
There is no additional requirement hidden in a counter's existential
auxiliary assignment. The retained definition is
`support/workspace/R4333Lean/SequentialAtMostCNF.lean`.

For byte-level decoding, let P(a,b) be b²+a when a<b and a²+a+b otherwise.
The sparse DIMACS edge variable is P(P(a,b),q)+1 and the counter variable
is P(tag,P(i,j))+1. For free row a=0,…,4, upper tags are 2704+8a+q and
lower tags 2708+8a+q. The mark tags are 2745 and 2749. Counter order is
row, color, upper/lower, followed by the two mark counters. Single-color
inputs follow physical vertex order. Complement lists group colors in
increasing order, then vertices in physical order within each color. Distinct tags separate all auxiliary namespaces from each
other and from the edge atoms. The 42 blocks contribute exactly
250,788 clauses. These definitions permit a direct inspection of the
frozen CNF directly from the published clause specification.
The independent [D base checker](../reproduce/d_base_check.py) implements
this specification directly, including the good-coloring clauses, all
template/free/mark units, exact counter inputs, namespaces and clause
order. The [retained run receipt](checks/D_BASE_CHECK.json) records exact
byte equality for all twelve owner/component bases through 18 stored
base or prefix comparisons: four sparse UUU/UUT bases and all fourteen
mixed-owner dense prefixes. The run used 4.83 CPU seconds and no solver,
certificate checker or Lean build. It does not check the finite cover
or per-leaf suffixes. To repeat that bounded check with a new receipt:

```sh
python3 reproduce/d_base_check.py --snapshot /path/to/extracted-evidence \
  --receipt /path/outside/evidence/new-d-base-check.json
```

D9 appends 30 signed units deciding x's color-3 membership at every vertex
of M and X, plus 65 positive cross-matrix units: 95 suffix clauses and
343,463 final clauses. D10 appends the same 30 membership units and 75
cross-matrix units: 105 suffix clauses and 343,473 final clauses. The
membership positives number nine and ten, respectively. Their free-C5
and foreign-support internal edges are already fixed by the base and
physical support choice. None of these suffixes specifies an internal
Q edge; the Q type belongs to the base.

## 6. From finite labels to exact native inputs

For UUU/UUT, `evidence/D/UUT/full_inputs_000/MANIFEST.json` retains both
parent descriptions, common sparse-to-dense maps, all 679 suffix arrays
and their identities. Its four/five UUT sparse bases are retained under
`bases/`; its UUU parents are the two original sparse bases under
`support/workspace/r4333_upper/`. At fixed physical coordinates, UUT
changes the appropriate 16 Q-template units, retaining every other base
clause. This statement concerns formula construction, not transfer of
satisfying assignments or UNSAT answers between owners.

Each mixed owner has its own
`evidence/D/mixed/full_inputs_KIND_000/MANIFEST.json`, dense prefix files,
dense maps and exact suffix arrays. The mixed decoder
`evidence/D/mixed/tools/mixed_d_leaf_units_001.py` carries the inverse
canonical orders into physical literals; the builder
`build_mixed_campaign_inputs_000.py` composes the intended bases, selected
finite labels and suffixes. The required units are 91/95/105 according
to branch, with the semantics in §5.

The portable source [reproduce/abd_inputs.py](../reproduce/abd_inputs.py)
reconstructs these exact inputs from the authenticated snapshot. For
UUU/UUT it remaps every sparse literal through the retained bijection;
for mixed D it uses the retained dense prefixes. It serializes each suffix
as one signed decimal literal followed by ` 0` and LF per clause, checks
all pinned hashes and dimensions, and checks the complete reconstructed
formula identity. Dense renaming preserves satisfiability. There are
4,900 dense variables for P15 and 131,570 for D9/D10. Prefix headers
already declare the final clause count; their base bodies are completed
by the suffix.

D10's full words are also literal data in
`ProfileDDegreeTenMatrixLeafDataUUU2P15.lean`: 82 words of 105 upper-triangle
colors, with nine ordered support-pair labels. Only the 75 cross-group
entries become matrix suffix units; the 30 internal entries are checked
against the existing free/support patterns. This data can be read without
executing Lean. The 408 D9 and 189 P15 suffixes are directly retained in
their native censuses, and all 679 are present in the reconstruction
manifest.

The mathematical coverage check establishes that every extracted host
reaches one of these labels. The encoding argument establishes that its
physical coloring extends to a satisfying valuation of the specified
base and suffix. Input reconstruction recovers the formula bytes and checks
their SHA-256 against the input hash in the retained native result. These are
separate obligations;
no one of the three substitutes for the others.

## 7. Trust scope

The [trust statement](TRUST_AND_CERTIFICATION.md) governs the computational
conclusion. The D exclusions have matching native UNSAT answers from Kissat
and CaDiCaL, joined to their exact input hashes. The complete
[A/B/D second-solver receipt](checks/ABD_SECOND_SOLVER.json) includes every D
owner. These native answers remain external computational evidence. Full per-leaf
D inputs are not archived; retained parent bases, finite data, maps, suffixes
and runner-recorded input hashes support exact reconstruction.
Native quiet logs and runner-recorded input hashes retain the limitations
described in the trust statement.

This supplement explains the physical extraction, exchange and encoding
implications and their finite data. The [Lean development](../formal/MATHEMATICS.md)
proves the corresponding complete D covers and native formula semantics,
including both original UUU/UUT owners. Its
[main theorem](../formal/src/PricingIntegration/NativeWholeProof.lean) consumes
the D exclusions through `AllNativeUnsat` over the concrete native formulas.
The [formula-binding tools](../formal/reproduce/README.md) connect those
Lean definitions to retained or reconstructed input bytes and runner-recorded
formula hashes. These external identity checks
and native UNSAT records retain their separate roles; the final
[formalization boundary](FORMALIZATION_STATUS.md) is the computational
unsatisfiability premise, not a mathematical cover or encoding parameter.
