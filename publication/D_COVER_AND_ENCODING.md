# The D cover and its physical formula semantics

This supplement gives the finite-cover and encoding details for
[the profile-D bound](../proof.md#4-the-a-b-and-d-ticket-bounds).
Every good four-coloring of K61 with a supplied profile-D root r and
H(r) at least 46 gives a satisfying assignment to one of 50,918
specified formulas. Each formula uses the complete 61-vertex physical
encoding.

## 1. An actual mark and its brace

Name the root cells R0,R1,R2,R3, of sizes 14,15,15,16 and root
colors 0,1,2,3. An endpoint p sends a ticket to r when its full
degree in the color of rp is at least 15. Only 44 neighbors lie
outside R3, so H(r) at least 46 supplies at least two ticket
senders in R3. Choose one as p.

Classify the three critical root cells. Their types are U-minus or
T-minus on R1,R2 and U or T on R3. Normalize p to reference position
15 of R3. The classification and fixed-palette template maps act on
whole actual cells, carrying every incident edge. One global physical
palette remains in force.

The actual critical neighborhood S=N3(p), called the brace, contains
the root and has no other member in R3. Put S_i=S intersect R_i for
i=0,1,2. Each support avoids both color 3 and its root color internally
and has at most five vertices. The supports total 14 or 15 vertices,
so their ordered sizes are (4,5,5), (5,4,5), (5,5,4) or (5,5,5).

Classification of the brace gives complementary colored five-cycles
inside every five-support and complementary colored four-vertex paths
inside its four-support, if present. The path conclusion uses the
classification of the actual brace as a one-vertex deletion of a
critical K16.

In the canonical D layout, the root is 0, R0 is 1 through 14,
R1 is 15 through 29, R2 is 30 through 44, and R3 is 45 through 60,
with mark 60. All 61 vertices remain present. Every vertex outside
the brace has negative marked-color membership, including the
vertices of R0 outside its selected support.

## 2. Normalized configurations

For each shape, enumerate the brace-template placements compatible
with the root and with fixed reference orders for its three colored
supports. For order 16, template transitivity fixes the reference
root. For order 15, include every eligible reference root. Reading
the colors between the ordered supports gives exactly 600 words per
shape: 100 from U and 500 from T. A word has 65 entries for shapes
(4,5,5), (5,4,5), (5,5,4) and 75 for shape (5,5,5).

For each foreign K15, enumerate every subset with the prescribed
colored path or cycle. Choose one representative with a fixed labeling
from each orbit under color-preserving automorphisms of the whole
K15 template. A support map must extend over its entire foreign cell.
The finite data give:

| Foreign template | Five-supports | Five-support orbits | Four-supports | Four-support orbits | Whole-template automorphisms |
|---|---:|---:|---:|---:|---:|
| U-minus | 11 | 3 | 60 | 8 | 10 |
| T-minus | 11 | 7 | 72 | 38 | 2 |

Put the free support on fixed vertices of R0 in reference order.
For fixed root-cell sizes and template types, a selected foreign
support pair and one of its 600 words form a normalized configuration.
It records the root spokes, all three template colorings, the internal
free-support pattern, the cross-support word and the exact equivalence

```math
c(pv)=3\quad\Longleftrightarrow\quad
v\in\{r\}\cup S_0\cup S_1\cup S_2\qquad(v\ne p).
```

Whole-template automorphisms normalize the foreign supports. A free
support labeling extends to a permutation of R0 because the complements
have equal size. The word may then be reduced using the foreign support
stabilizers and the free path or cycle automorphisms, of orders 2 or 10.
These maps extend over all 61 vertices. They carry both positive and
negative membership facts and all other edge colors together.

## 3. The finite coverage condition

Every retained list is checked against the same condition: for each
normalized support pair and every word, there is a retained case and a
symmetry of the full host such that every required target fact pulls
back to a recorded source fact. The symmetry consists of one vertex
permutation and one global color permutation. Its check includes the
complete signed membership relation.

This criterion is sufficient because the source configuration comes
from an actual good coloring. Transport that coloring by the specified
symmetry. Every target fact holds, and goodness is preserved, so the
transported coloring satisfies the retained case's formula.

Exchanging R1 and R2 together with colors 1 and 2 is one such whole-host
symmetry. Fixed-palette maps restore the foreign templates; a
palette-realizing vertex map fixing the mark restores R3, and a
free-support relabeling restores its reference order. This identifies
TU with UT and, when the foreign types agree, identifies shapes (5,4,5) and
(5,5,4). For TT in shapes (4,5,5) and (5,5,5), the two five-support orbit
indices are ordered, retaining all words on a diagonal pair. Both marked
template choices are included.

The retained counts for each marked type are:

| Foreign types | (4,5,5) | (5,4,5) | (5,5,4) | (5,5,5) | Total |
|---|---:|---:|---:|---:|---:|
| UU | 189 | 408 | through exchange | 82 | 679 |
| UT | 1,824 | 1,992 | 2,388 | 372 | 6,576 |
| TT | 5,256 | 11,892 | through exchange | 1,056 | 18,204 |

The first two letters in UUU, UUT, UTU, UTT, TTU and TTT name the
foreign cells; the third names the marked cell. The complete D
boundary therefore has

```math
2(679+6,576+18,204)=50,918
```

formulas. Completeness is established by the finite coverage condition
on all normalized configurations. The formal implementation is in
[CommonCover](../formal/src/UniformK61/CommonCover.lean),
[UUPhysicalCover](../formal/src/UniformK61/UUPhysicalCover.lean),
[UUFiniteCover](../formal/src/UniformK61/UUFiniteCover.lean) and
[UnitTransport](../formal/src/UniformK61/UnitTransport.lean).

## 4. Formula semantics

Every D formula is the shared base of 7,320 physical edge-color
variables and 156,770 clauses, followed by ordered signed edge units.
The base imposes exactly one color on every edge of K61 and prohibits
every monochromatic triangle. The marked formulas have no auxiliary
variables.

The units fix all 60 root spokes, the three root-cell templates,
the free-support pattern, the cross-support word and exact marked
membership. For every nonroot vertex other than the mark, its
marked-color unit is positive on the selected supports and negative
elsewhere. The root-mark edge is already fixed by its root spoke.

Assign each physical variable the truth value of its statement about
the transported host. Goodness satisfies the base, and the coverage
condition supplies every unit. This implication is established by
[Core.coloring_satisfies_formula](../formal/src/UniformK61/Core.lean).
The exact unit lists are defined in
[CommonFormula](../formal/src/UniformK61/CommonFormula.lean) and
[MarkedUU](../formal/src/UniformK61/MarkedUU.lean).
[uniform_k61.py](../reproduce/uniform_k61.py) generates their inputs;
the [A/B/D data index](ABD_EVIDENCE_INDEX.md) locates the finite data
and exact-input checks.

## 5. Consequence and verification scope

If all 50,918 exact D formulas are unsatisfiable, a good host with a
D root and H(r) at least 46 would satisfy one of them, a contradiction.
Thus H(r) is at most 45 at every D root. This is
[ABDProof.D_selected_excluded](../formal/src/UniformK61/ABDProof.lean),
used in the global ticket-counting argument.

Lean proves mathematical coverage and the host-to-formula implications.
The [binding tools](../formal/reproduce/uniform/README.md) compare every
emitted formula with the current input catalog. Native acceptance checks
Kissat and CaDiCaL UNSAT records for each exact input. These external
results supply the computational premise of
[WholeProof.ramsey61](../formal/src/UniformK61/WholeProof.lean), under the
[stated verification method](TRUST_AND_CERTIFICATION.md).
