# The mathematics behind the search

The proof of $R(3,3,3,3)\leq61$ combines local classifications with a global
double-counting argument. Its main challenge is to extract a small exhaustive
family from a hypothetical coloring while preserving the requirement that
every local description belongs to the same graph. This page explains the
choices behind the construction; [proof.md](proof.md) gives the complete
argument and [the reproduction guide](publication/REPRODUCIBILITY.md)
provides executable checks.

## Neighborhoods supply the finite structure

Fix a vertex of a four-colored complete graph with no monochromatic
triangle. Its neighbors split into four groups according to the colors of
their edges to that vertex. A group omits its connecting color internally,
so it is a good three-colored complete graph. Each group has at most 16
vertices. Since their sizes sum to 60, the sorted sizes are one of

```math
(12,16,16,16),\quad(13,15,16,16),\quad(14,14,16,16),\quad
(14,15,15,16),\quad(15,15,15,15).
```

These are profiles A through E. The neighborhoods of orders 15 and 16 have
a small classified family, represented by two reference templates U and T
with the appropriate deletion at order 15. The repository proves the
classification locally in Lean, using 55 finite certificate checks.

Profile C presents a different difficulty from A, B and D: two of its
neighborhoods have only 14 vertices, so the critical templates do not apply
to them. Treating those neighborhoods as arbitrary parts of the same
61-vertex graph is essential to an exhaustive cover.

## A marked vertex connects the local descriptions

An endpoint is high on an edge if its degree in that edge's color is at
least 15. Marking a high endpoint supplies another actual critical
neighborhood. Its intersections with the root neighborhoods have four or
five vertices, with tightly constrained internal colors. These intersections
are the supports used in the finite case enumeration.

For each fixed choice of root-cell sizes and templates, a normalized
configuration records selected support positions and one of the 600 words
describing their cross colors. It also records the root and template edges
and exact marked-neighborhood membership. Whole-template automorphisms and
support stabilizers reduce this finite boundary.

Every retained list meets the same coverage condition: each normalized
configuration maps to a listed case through one permutation of all 61
vertices and one global color permutation, with every target fact supplied
by a recorded source fact. This includes negative membership for vertices
outside the selected supports. The formal cover proves that all facts hold
simultaneously in the transported host coloring.

For profiles A, B and D, ruling out the resulting marked configurations
establishes local incidence inequalities. These inequalities hold at every
vertex of the corresponding profile. The computation does not need to
exclude each profile separately.

## Double counting leaves two concrete alternatives

A high endpoint sends a ticket across its edge. Double counting these
tickets, once at the sender and once at the receiver, equates the total
number sent with the total number received. The A/B/D inequalities bound
how many tickets a vertex can receive.

One alternative is an entrance: a C root with a high endpoint in a
14-vertex neighborhood.
That endpoint supplies the marked neighborhood, and its supports with the
root's two size-16 neighborhoods have an exhaustive 346-case cover. The
other vertices remain free except for the common graph clauses and exact
membership facts. In particular, there is no critical template imposed on
either size-14 root neighborhood.

Without an entrance, every vertex receives at most as many tickets as it
sends. Double counting forces equality at every vertex, giving perfect
balance. Only C and E profiles remain, and every ticket is reciprocated.
Degree and connectivity arguments rule out E and force the same two colors
to have degree 16 at every vertex. The other two colors have degree 14.

## Perfect balance becomes three full-graph cases

Normalize the two size-16 neighborhoods at a root to U or T. Exchanging
the two high colors identifies UT with TU, leaving UU, UT and TT. The
balanced formulas forbid monochromatic triangles in the whole graph and
encode the visible parts of actual critical neighborhoods.

For each vertex in either size-16 root neighborhood, the neighborhood in
the opposite high color also has order 16. Classification therefore gives
an ordinary U/T template embedding. The formula encodes the visible parts
of these neighborhoods inside the two root cells, requiring their edge
predictions to agree with the same physical edge variables. Five-vertex supports give a small finite
normalization of each embedding. These are consequences of the existing
critical-neighborhood classification, and the complete normalization and
encoding are checked in Lean.

The three formulas include all 61 vertices and all of their edges. Their
unsatisfiability closes the balanced alternative directly.

## One host throughout the computation

Every case shares 7,320 physical variables and 156,770 base clauses. The
marked A/B/D and C formulas add signed edge facts. The balanced formulas
also use auxiliary variables for support choices and local template
embeddings, giving 13,656 variables and 524,462 clauses each.

The complete cover has 56,723 formulas: 360 for A, 5,096 for B, 50,918 for D,
346 marked C cases and three balanced C cases. Every formula is assigned
to Kissat and CaDiCaL with default options and no CPU or wall-clock limit.
The [cost report](publication/MEASURED_COSTS.md) separates their measured CPU
time from elapsed duration, Lean compilation and input verification.

Three obligations connect these computations to the theorem. Every good
host must reach a listed case; its actual colors and suitable auxiliary
values must satisfy that case's exact formula; and that formula must be
unsatisfiable. Lean establishes the first two obligations. Native solver
results supply the third under the documented
[verification standard](publication/TRUST_AND_CERTIFICATION.md). Complete
input comparisons connect the Lean definitions to the solver bytes.

The work was developed with extensive AI assistance, described in
[the attribution statement](publication/ATTRIBUTION.md). The mathematical
argument and computational package are supplied for independent review.
