# The mathematics behind the search

The proof of $R(3,3,3,3)\leq60$ combines local classifications with a global
double-counting argument. Its main challenge is to extract a small exhaustive
family from a hypothetical coloring while preserving the requirement that
every local description belongs to the same graph. This page explains the
choices behind the construction; [proof.md](proof.md) gives the complete
argument and [the reproduction guide](REPRODUCIBILITY.md) provides executable
checks.

## Neighborhoods supply the finite structure

Fix a vertex of a four-colored complete graph with no monochromatic
triangle. Its neighbors split into four groups according to the colors of
their edges to that vertex. A group omits its connecting color internally,
so it is a good three-colored complete graph. Each group has at most 16
vertices. Since their sizes sum to 59, the sorted sizes are one of

```math
(11,16,16,16),\quad(12,15,16,16),\quad(13,14,16,16),\quad
(13,15,15,16),\quad(14,14,15,16),\quad(14,15,15,15).
```

These are profiles A, B, C1, D, C2 and E. The neighborhoods of orders 15
and 16 have a small classified family, represented by two reference templates
U and T with the appropriate deletion at order 15. The repository proves the
classification locally in Lean, using 55 finite certificate checks.

The C profiles present a different difficulty: two root neighborhoods have
only 13 or 14 vertices, so the critical templates do not apply to them.
Treating those neighborhoods as arbitrary parts of the same 60-vertex graph
is essential to an exhaustive cover.

## A marked vertex connects the local descriptions

An endpoint is high on an edge if its degree in that edge's color is at
least 15. Marking a high endpoint supplies another actual critical
neighborhood. Its intersections with the other root neighborhoods have
four or five vertices, with tightly constrained internal colors. These
intersections are the supports used in the finite case enumeration.

For each fixed choice of root-cell sizes and templates, a normalized
configuration records selected support positions and one of the 600 words
describing their cross colors. It also records the root and template edges
and exact marked-neighborhood membership. Whole-template automorphisms and
support stabilizers reduce this finite boundary. A marked 15-vertex cell has
three possible mark orbits in U-minus and nine in T-minus.

Every retained list meets the same coverage condition: each actual
configuration maps to a listed case through one permutation of all 60
vertices and one global color permutation, with every target fact supplied
by the actual coloring. This includes negative membership for vertices
outside the selected supports. The formal cover proves that all facts hold
simultaneously in the transported host.

For profiles A, B, D and E, ruling out the resulting marked configurations
establishes strict local ticket bounds. These inequalities hold at every
vertex of the corresponding profile. The computation does not need to
exclude each profile separately.

## Double counting leaves two concrete alternatives

A high endpoint sends a ticket across its edge. Double counting these
tickets, once at the sender and once at the receiver, equates the total
number sent with the total number received. The A/B/D/E inequalities bound
how many tickets a vertex can receive.

One alternative is an entrance: a C1 or C2 root with a high endpoint in a
noncritical neighborhood. That endpoint supplies the marked neighborhood,
and its supports with the root's critical neighborhoods have exhaustive
covers of 692 and 7,840 cases. The other vertices remain free except for the
common graph clauses and exact membership facts. No critical template is
imposed on either small root neighborhood.

Without an entrance, every vertex receives at most as many tickets as it
sends. Double counting forces equality at every vertex, giving perfect
balance. The strict bounds leave only C1 and C2, and every ticket is
reciprocated.

## Critical neighborhoods have one common pair of colors

Every vertex now has exactly two critical colors. Reciprocity and the
connectivity of critical color graphs first show that a critical
neighborhood is homogeneous: all its vertices have the same critical pair.

Apply this observation again inside a critical neighborhood. If its pair
introduced a color that is noncritical at the root, the second homogeneous
neighborhood could meet only two root cells. Each intersection has at most
five vertices, which cannot fill a neighborhood of order at least 15.
This forces one common pair throughout the graph.

After one global color permutation, every degree vector is
`(16,16,14,14)` minus a single coordinate unit. C1 vertices have both high
degrees equal to 16; C2 vertices have high degrees 15 and 16. The balanced
formulas retain this mixture at other vertices.

## Perfect balance supplies an actual brace

Three auxiliary exclusions rule out the possibility that all vertices have
profile C1. Choose a C2 root and any mark in its 15-vertex critical cell.
The mark's critical neighborhood is an actual subgraph of order 15 or 16.
It meets the other root cells in supports of sizes four or five. After
exchanging the two low colors, the possible shapes are 455, 554 and 555.

The root has one full 16-vertex template, one 15-vertex template, and two
14-vertex cells. Only the selected five vertices of one low cell receive a
cycle constraint; there is no full critical template on that cell. The
brace fixes colors between these parts. Its exhaustive cover has 720
cases: 624 with a 15-vertex brace and 96 with a 16-vertex brace.

The balanced formulas also describe the visible parts of 26 actual
opposite-color neighborhoods. Each has a five-vertex anchor, so six
normalized template tables suffice. A witness assigns distinct template
positions to the visible members and requires all predicted edges to agree
with the same physical coloring. The remaining four- or five-vertex support
conditions are retained as guards. These constraints can expose incompatible
local descriptions before a solver explores many unconstrained graph edges.

## One host throughout the computation

Every case shares 7,080 physical variables and 149,270 base clauses. The
marked A/B/D/E and entrance formulas add signed edge facts. The balanced
formulas also use auxiliary variables for degree bounds, support choices
and local template embeddings.

The complete cover has 296,797 formulas: 56,374 for A/B/D, 231,168 for E,
8,532 entrances, three all-five exclusions and 720 marked balanced cases.
Every indexed formula requires a direct Kissat UNSAT outcome. The evidence
retains all attempts; a timeout or interrupted attempt does not exclude a
case, and an invalid or conflicting history blocks acceptance.

Three obligations connect these computations to the theorem. Every good
host must reach a listed case; its actual colors and suitable auxiliary
values must satisfy that case's exact formula; and that formula must be
unsatisfiable. Lean establishes the first two obligations. Native solver
results supply the third under the documented
[verification standard](proof.md#9-formal-theorem-and-computational-boundary).
Complete input comparisons connect the Lean definitions to the solver bytes.

The work was developed with extensive AI assistance, described in
[the attribution statement](publication/ATTRIBUTION.md). The mathematical
argument and computational package are supplied for independent review.
