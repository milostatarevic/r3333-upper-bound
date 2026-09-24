# A computer-assisted proof of $`R(3,3,3,3)\leq61`$

## The result

The Ramsey number $`R(3,3,3,3)`$ is the least integer n such that every
four-coloring of the edges of the complete graph $`K_n`$ contains a
monochromatic triangle. We prove that n=61 has this property.

A SAT formula is a logical constraint on Boolean variables. Here formulas
are written in conjunctive normal form (**CNF**): an AND of clauses, each
an OR of variables or their negations. **UNSAT** means that no assignment
of truth values satisfies the formula.

**Theorem.** Every four-edge-coloring of $`K_{61}`$ contains a monochromatic
triangle. Equivalently,

```math
R(3,3,3,3)\leq61.
```

The proof combines combinatorial reductions, exhaustive finite calculations,
and SAT refutations. The reductions preserve a single hypothetical coloring
through an exhaustive cover of exact formulas. The retained evidence contains
the finite tables, their checks, the encoded inputs and the native UNSAT
results; all 56,830 formulas have matching answers from Kissat and CaDiCaL.
Section 10 describes the formalization and verification
status separately from the mathematical argument.

We call an edge coloring **good** if it has no monochromatic triangle. We
write $`K_n`$, $`C_n`$ and $`P_n`$ for a complete graph, cycle and path on n vertices.
A *root* is simply a distinguished actual vertex of one hypothetical good
coloring. An *actual* vertex or edge belongs to that coloring; a *reference*
position is a coordinate used in a smaller critical template. In particular,
a reference position added to complete a K15 is not an extra host vertex.

All reductions below preserve one coloring. A vertex relabeling carries
every incident edge. A permutation of colors applies to the whole graph,
including the root spokes. On overlapping neighborhoods, shared physical
vertices and edge colors must agree. No independently satisfiable collection
of local neighborhoods is assumed to extend to a common host.

The argument first obtains restrictions on degrees at every vertex. A
conservation identity then forces a suitable distinguished vertex unless
one special regular-overlap configuration occurs. That configuration is
excluded by finite local compatibility checks. The distinguished vertex
produces an exhaustive cover by full-host SAT formulas, whose refutations
finish the argument.

Bracketed references [E1], [E2], … locate exact archived mathematical and
computational evidence in Appendix A. The
[classification provenance](publication/CLASSIFICATION_PROVENANCE.md) records
the historical attribution of the smaller-order classifications established
in the supplied Lean development.
The [verification map](publication/MATHEMATICS.md),
[A/B/D evidence index](publication/ABD_EVIDENCE_INDEX.md) and
[dependency ledger](publication/DEPENDENCIES.json) connect the argument to
its exact data, source files and check records.

## 1. Critical neighborhoods

The elementary inequalities $`R(3,3)\leq6`$ and $`R(3,3,3)\leq17`$ suffice for
the degree bounds below. For the first, a vertex in K6 has three incident edges
of one color. Either an edge among their endpoints has that color, or the three
endpoints form a triangle in the other color. For the second, a vertex in K17
has six neighbors in one of three colors, and their induced coloring uses only
the other two colors.

The nontrivial classification used by the finite reductions is the following.

**Critical-neighborhood theorem.** Every good three-coloring of K16 is weakly
isomorphic to one of two explicit colorings, denoted U and T. Every good
three-coloring of K15 is a vertex deletion of one of these K16 colorings. In
each critical K16, each individual color graph is the Clebsch graph. Weak
isomorphism allows a vertex permutation and one permutation of the three
colors. The literal U/T matrices used here are fixed data [E4]. The K15
templates delete vertex 15, as defined by `k15Untwisted` and `k15Twisted` in
[CriticalTemplates.lean](formal/src/R4333Lean/CriticalTemplates.lean).
Completeness and coordinate conventions are separate assertions.

The proof uses the project's own Lean classification development. Its
source closure and finite CNF/LRAT payloads are supplied in
[`classification/`](classification/); the
[classification provenance](publication/CLASSIFICATION_PROVENANCE.md)
identifies the exact theorem endpoints, their logical assumptions and the
supporting checks. A fresh rebuild checked all 32 modules and 55 CNF/LRAT
pairs; a separate adapter also connects their catalogue conclusions to actual
physical neighborhoods of the 61-vertex host. The literal matrices used by
the present encoders are also retained [E4]. The local kernel checks establish the required smaller-order structure.

The K16 classification is historically due to Kalbfleisch and Stanton,
and the K15 classification to Heinrich. The locally supplied proofs and
certificate data establish the versions used here [E1–E4].

The explicit templates admit all six palette permutations through vertex
maps and are color-preservingly vertex-transitive at order 16. The retained
palette symmetry source [E5]
and mark/deletion source [E6]
give these maps. Applying a map to one disjoint root block is a vertex
relabeling of that block and all its incident edges. This can absorb a weak
catalogue palette without independently recoloring a shared edge. When two
neighborhoods overlap, their maps must instead agree on the overlap; Sections
4 and 8 impose that agreement explicitly.

No extension theorem for an arbitrary K14 is used. Completing a K15 in the
classification is local: the formal sixteenth reference position does not
become a vertex of K61 or a common completion vertex for different scopes.

## 2. Degrees, profiles, and the incidence identity

Let $`c(uv)\in\{0,1,2,3\}`$ be the edge color, and define

```math
N_i(v)=\{u\ne v:c(uv)=i\},\qquad d_i(v)=\lvert N_i(v)\rvert.
```

The coloring induced on $`N_i(v)`$ is a good three-coloring, so $`d_i(v)\leq16`$.
Since the four degrees sum to 60, each is at least 12. The four deficits

```math
16-d_0(v),\ldots,16-d_3(v)
```

are nonnegative integers summing to four. We will use their unordered
partitions after introducing two incidence counts.

An endpoint $`u`$ is **high on its edge to v** when

```math
d_{c(uv)}(u)\geq15.
```

Define

```math
\begin{aligned}
H(v)&=\bigl\lvert\{u\ne v:d_{c(uv)}(u)\geq15\}\bigr\rvert,\\[2pt]
w(v)&=\sum_{i:d_i(v)\geq15}d_i(v).
\end{aligned}
```

Thus H counts highness at the *other* endpoint, while w counts highness at
the vertex itself. Reversing ordered pairs $`(v,u)`$ proves the exact identity

**(1)**

```math
\sum_v H(v)=\sum_v w(v).
```

The partitions of the four deficits give exactly five sorted degree
**profiles**. We name them A, B, C, D and E; the last column follows from
the definition of w. A statement such as A(v) means that v has profile A.

| Profile | Sorted degrees | Ordered versions | $`w(v)`$ |
|---|---|---:|---:|
| A | 12,16,16,16 | 4 | 48 |
| B | 13,15,16,16 | 12 | 47 |
| C | 14,14,16,16 | 6 | 32 |
| D | 14,15,15,16 | 12 | 46 |
| E | 15,15,15,15 | 1 | 60 |

A C vertex r is called **eligible** when H(r)≥32. This is a condition on
that same vertex in the original coloring, not a license to replace it by
an auxiliary center later in the argument.

The 35 ordered profile vectors in the full-host C encoder are precisely the
4+12+6+12+1 vectors above, not a restriction to C/E vertices. The retained
composition review [E7]
checks this elementary entrance and the use of (1).

## 3. Excluding high-H roots of profiles A, B and D

The finite calculations and SAT refutations below establish the following
implications for **every vertex** of one hypothetical good K61:

```math
\begin{aligned}
A(v)&\Longrightarrow H(v)\leq47,\\[2pt]
B(v)&\Longrightarrow H(v)\leq46,\\[2pt]
D(v)&\Longrightarrow H(v)\leq45.
\end{aligned}
```

Call these three inequalities **(X)**, or selector-X. They do not say that
vertices of these profiles are absent. Nor is v required to maximize H.
The finite extractions begin
with an arbitrary supplied root satisfying the contrary threshold, and use
only that root, its actual coloring, and the smaller-order facts above.
This quantifier is essential to applying (1) at all vertices later.

### 3.1 Common marked-neighborhood extraction

Write the root-color cells as $`F,M,X,Q`$, of colors $`0,1,2,3`$, where F is
the low block and Q is a K16. In A, B, D their sizes are respectively

```math
(12,16,16,16),\quad(13,15,16,16),\quad(14,15,15,16).
```

There are only 44 nonroot vertices outside any particular K16. Hence H at
least 48, 47, 46 supplies at least four, three, two genuinely high endpoints,
respectively, in that K16. Choose one, x, in Q, and normalize its position by
a color-preserving automorphism of the *whole* Q template.

There is no color-3 edge inside Q. The color-3 neighbors of x in each of
F,M,X induce good two-colored cliques, so each support has at most five
vertices. Since the root itself contributes one color-3 neighbor of x,
the three support sizes must be

**(2)**

```math
(4,5,5),\quad(5,4,5),\quad(5,5,4),\quad(5,5,5).
```

Retain all three critical blocks M,X,Q and exactly the four or five actual
support vertices in F. Restore the root only when classifying the complete
color-3 neighborhood of x. That neighborhood has order 15 or 16, so its
root-cell pieces are colored C5s, or complementary colored P4s in the short
cell. An arbitrary good two-colored K4 need not be a P4 in each color; the
P4 conclusion here comes from the K15-to-K16 critical classification.

For each ordered shape in (2), the retained local construction takes both
critical types, all eligible rooted positions, and every color-preserving
isomorphism of each support to its canonical P4/C5. Reading the cross edges
gives a complete set of **600 matrix words**, 100 from U and 500 from T.
These are labeled local matrices, not 600 isomorphism types. For fixed
physical foreign supports, only automorphisms extending to their *entire*
physical U/T blocks are used to identify words. Free-support permutations
must preserve its colored P4/C5. The inverse of the canonical labeling maps
every cross edge back to its physical endpoints.

This describes a finite exhaustive procedure, not an argument from the
number 600. The explicit matrix construction [E8]
specifies the procedure; each formula family has an independent finite check
of the supports, extending actions, complete matrix orbits and case IDs.
A word such as UUT records the U/T types of the three physical critical
root blocks, in their stated order; we call this word the family's **owner**.
It does not specify the type of the marked endpoint's restored neighborhood.
That neighborhood is classified separately, and both restored types remain
in every applicable stage.

### 3.2 A and B: retain their actual stronger geometry

For A, prefer a high mark in a T block if a T block exists. A simultaneous
permutation of the three equal K16 blocks and their root colors leaves four
owners UUU, UUT, UTT, TTT, with the marked block last. For B, the first
critical block has size 15 and cannot be swapped with a K16. A simultaneous
exchange of the two K16 blocks, with palette compensation on the other
block, gives six preferred owners. Every needed foreign deficiency
orientation in (2) is retained.

| A owner | 455 | 545 | 554 | 555 | Total |
|---|---:|---:|---:|---:|---:|
| UUU | 4 | 4 | 4 | 2 | 14 |
| UUT | 4 | 4 | 4 | 2 | 14 |
| UTT | 16 | 16 | 20 | 4 | 56 |
| TTT | 76 | 92 | 92 | 16 | 276 |
| **Total** | | | | | **360** |

| B owner (M15,X16,Q16) | 455 | 545 | 554 | 555 | Total |
|---|---:|---:|---:|---:|---:|
| UUU | 36 | 40 | 36 | 10 | 122 |
| UUT | 36 | 40 | 36 | 10 | 122 |
| UTT | 168 | 184 | 204 | 36 | 592 |
| TUU | 168 | 220 | 168 | 36 | 592 |
| TUT | 168 | 220 | 168 | 36 | 592 |
| TTT | 828 | 1084 | 996 | 168 | 3076 |
| **Total** | 1404 | 1788 | 1608 | 296 | **5096** |

The direct formulas keep the full critical tail of size 48 for A and 47 for
B, plus k=4 or 5 actual free support vertices. The root is implicit: its
spoke is restored in its own color, giving a rootless cap of 15 in that
color and 16 in the other colors. All retained edges are one-hot colored
and all retained triangles are constrained.

For a retained free vertex, let $`t_i`$ count its color-i edges into the
full retained critical tail. Its full F-internal nonzero degrees lie in
1..5 for A and 2..5 for B: their sums are respectively 11 and 12 and each
is at most five. Consequently the necessary tail intervals are

| Bound | A | B |
|---|---|---|
| $`t_0`$ | 11..15 | 11..15 |
| $`t_i, i\ne0`$ | 7..15 | 7..14 |
| $`t_0+t_i, i\ne0`$ | at least 22 | at least 22 |

For the last inequality, the other two full color degrees are at most 32,
so $`d_0+d_i\geq28`$; subtract the root edge and at most five F-internal
color-i edges. The upper bounds for A and B must not be replaced by the
stronger D upper bound 13.

A critical-tail vertex has own nonzero color count at least six into the
tail and other nonzero counts at least seven, after subtracting at most
five F neighbors and, in its own color, the root. Its color-0 degree in
the retained graph is at least k for A and k−1 for B.

Highness is represented by selectable necessary proxies. A genuinely high
tail vertex has own-color tail degree at least nine, and a genuinely high
free vertex has $`t_0\geq14`$. At least $`36+k`$ true highs survive in A,
and $`34+k`$ in B, because only $`12-k`$ or $`13-k`$ low-cell vertices were
deleted. Assign those proxies true and the mark's proxy true. The formulas
require the corresponding implications and total, not an invalid converse
saying that every partial-model proxy is genuinely high in a completed K61.

These arguments construct a satisfying valuation from every host under
the supplied-root hypothesis, including all zero-covered cases. They
make no zero-free donor or recoloring assumption. The source derivations and
their separate finite/input acceptances are:

- A: hand cover [E9],
  independent extraction [E10],
  finite acceptance [E11],
  input acceptance [E12].
- B: hand coverage review [E13],
  exact formula specification [E14],
  finite acceptance [E15],
  actual input review [E16].

### 3.3 D: the U/U and mixed foreign-block covers

The D extraction keeps a 46-vertex critical tail and four or five actual
free support vertices. Its nonzero full-F internal degrees are 3..5;
hence the free-row tail intervals are $`t_0\in[11,15]`$ and
$`t_i\in[7,13]`$ for $`i\ne0`$. The four-support branch gives an actual
marked K15 neighborhood; the five-support branch leaves nine or ten
color-3 neighbors in the two foreign K15 blocks. The component
names P15, D9 and D10 refer to these distinctions, not to host orders.

For two foreign U15 blocks the retained complete boundary is

**(3)**

```math
189\text{ P15}+408\text{ D9}+82\text{ D10}=679.
```

The P15 cover first has 372 ordered matrix labels and is reduced to 189
through a proved exchange of equal foreign blocks. D9 normalizes the two
deficiency orientations and retains a restored-U root-2 family of 72
labels and restored-T root-1, root-4 and root-12 families of 132,132,72.
D10 retains 82 ordered support/matrix labels. P15's matrix-only formulas
are weaker than the full extraction; UNSAT of the weaker formulas still
contradicts a host. Their answers are not inferred from stronger
position-specific formulas.

For UUT, replacing the marked Q16 type changes its actual template clauses.
The local marked neighborhood contains no other Q vertex, so the
foreign-U support geometry and finite data in (3) remain applicable. A
Q-sensitive foreign exchange uses a palette-realizing Q map composed with
color-preserving transitivity to fix the marked coordinate. It acts on
every Q incident edge. Thus UUT has the same *number* of labels but its own
679 newly searched formulas; UUU UNSAT answers are not reused as UUT answers.
See the UUT cover and transport [E17]
and its independent review [E18].

For foreign U15/T15, the actual support orbits and stabilizers change.
U15 has three proper five-support orbits and eight proper four-support
orbits; T15 has seven and 38. The complete independent finite check verifies
the Cartesian support products and all 600 words for each pair. Both
deficiency orientations remain:

| Foreign types | P15 | First foreign support short | Second foreign support short | D10 | Required per Q type |
|---|---:|---:|---:|---:|---:|
| UT | 1824 | 1992 | 2388 | 372 | 6576 |
| TT, full ordered data | 9084 | 11892 | 11892 | 1824 | 34692 before the next reduction |
| TT, retained cover | 5256 | 11892 | covered by exchange | 1056 | 18204 |

For TT, exchange equal foreign blocks with the single global color swap
1↔2 and restore Q by its marked palette lift. Order the two five-support
orbit indices before choosing a matrix. Keep i≤j, retaining **every**
matrix representative on diagonal pairs. This gives 28 support pairs,
5256 P15 and 1056 D10 words; it is not halving arbitrary matrix counts.
The same exchange covers the other D9 deficiency orientation. UT cannot
make that reduction within one ordered foreign-type frame.

The mixed cover design [E19],
TT exchange proof [E20],
finite data review [E21],
and complete input review [E22]
bind these logical choices to actual formulas.

The required D families have 679 cases for UUU, 679 for UUT, 6576 for
UTU, 6576 for UTT, 18204 for TTU, and 18204 for TTT. U/T labels are ordered by the two foreign K15s and then Q16.
Exchanging the equal K15 roles accounts for the omitted ordered TU cases.

The [D cover and encoding specification](publication/D_COVER_AND_ENCODING.md)
states the whole-host coordinate maps, exhaustive label construction and
necessary CNF constraints together. It supplies the coordinate-change
argument directly, using the explicit templates and finite data indexed there.

### 3.4 The resulting incidence bounds

For each of the listed families, the finite computation checks the complete
support and matrix cover, the encoder audit binds each representative to its
necessary formula, and the native computation reports UNSAT for every such
formula. The precise hypothesis is unsatisfiability of every exact formula
in that cover, not merely equality of two reported case counts.

Under those hypotheses, any root with A/H≥48, B/H≥47 or D/H≥46 would
produce a satisfying assignment of a formula in its corresponding family.
This is a contradiction. Therefore (X) holds at every vertex. This argument
uses neither a C exclusion nor a maximum-H choice of root.

The native result inventory [E23], complete evidence join [E24] and UUU
same-host semantic join [E25] identify the computations used here. All 56,374
A/B/D inputs have recorded Kissat UNSAT answers and matching CaDiCaL 3.0.1
UNSAT answers from the complete
[second-solver rerun](publication/checks/ABD_SECOND_SOLVER.json).
The reconstruction tools recover each exact
formula from the retained bases and finite data. Full per-case A/B/D CNFs
are not retained in the archive; reconstruction is checked against the input
SHA-256 recorded by the corresponding solver runner. Section 10 states the
verification standard.

## 4. The local Clebsch completion relation

The G and C covers use a compact common relation that merits an explicit
description. Represent the Clebsch graph K on

```math
\Gamma=\mathbb F_2^5/\langle(1,1,1,1,1)\rangle
```

with generators $`s_1,\ldots,s_5`$, whose sum is zero. Vertices differing by
one generator are adjacent. K has 16 vertices, degree five, no triangles,
and two common neighbors for each pair of distinct nonadjacent vertices.
Its complement has 80 edges.

Equivalently use even subsets of five indices, with adjacency when the
symmetric difference has size four. Translate an independent set to contain
the empty set. The other vertices are pairwise-intersecting two-subsets.
Four distinct such pairs must share one index, so every independent
five-set is the neighborhood of a unique center. For an independent
four-set, its three pairs either share an index (**star-four**) or are
ab,ac,bc (**nonstar-four**). The latter forms an affine binary plane.

Fix K as one color graph. Color each complementary edge by a sign ±1 for
the other two distinguished colors. Every K-neighborhood is a five-clique
in the complement and must be a colored C5. At each vertex of that clique,
the four signs therefore sum to zero. Over $`\mathbb F_3`$ this is equivalent
to integer balance when all signs are nonzero. Every complementary triangle
lies in one of these five-cliques: after translating one vertex to zero,
the other two are generator pairs sharing an index, which gives their common
K-neighbor. These balance equations are thus an exact three-color goodness
condition, not only a marginal relaxation.

Write $`f_{ij}(x)`$ for the sign on direction $`s_i+s_j`$. Edge symmetry and
the five balance equations give

**(4)**

```math
f_{ij}(x+s_i+s_j)=f_{ij}(x),\qquad
                  \sum_{j\ne i}f_{ij}(x)=0.
```

Fourier analysis over $`\mathbb F_3`$ gives dimension 15: the trivial
character contributes five, the ten characters with two negative generator
signs contribute zero, and each of the five with four negative signs
contributes two. For a given direction, the three possible nonconstant
characters are independent. Two nonzero coefficients would force a zero
value somewhere; one character coefficient requires zero constant.
The full-support solutions consequently consist of:

- 12 constant-direction solutions, indexed by a labeled five-cycle;
- 60 single-twist solutions: five excluded indices, three alternating
  four-cycles, two alternating signs, and two remaining constant choices.

This is exactly **72 labeled completions with the two low colors distinguished**.
The full hand derivation [E26]
proves both directions and the full-support classification. The independent
finite execution derived rank 65/nullity 15 from the 80 balance equations and
tested all $`2^{15}`$ sign assignments of free coordinates, retaining exactly
the same 72 full-support states. The accepted
reference relation [E27]
and summary [E28] are shared
data for subsequent checks.

Conditioning on a fixed colored five-anchor leaves **six** completions:
one constant state U and five twists $`T_t`$. If the anchor cycle has signs
$`c_{ij}`$, let $`C_t`$ be its unique alternating four-cycle on the indices
other than t. On a direction ij in $`C_t`$, the twist is

**(5)**

```math
-c_{ij}\chi_t(x),
```

and off $`C_t`$ it is the constant $`c_{ij}`$. This fixes the signs on the
actual anchor, because $`\chi_t(s_i)=-1`$ there.

We use **scope** to mean an actual color neighborhood when examining its
local constraints inside the shared host. For an actual K15 scope containing
a full five-anchor Q, its omitted K16
reference position is outside Q. Every known physical member outside Q
has a complete mask of either five anchor neighbors (the center), or a
distinct pair of anchor neighbors (one of ten pair roles), in the designated
Clebsch color. These roles must be injective and agree with known mutual
edges. Missing positions stay absent. The partial-scope proof [E29]
establishes this interface, including the uniqueness of the colored K10
restriction given two actual disjoint five-anchors. Separate scopes always
refer to the same variable for the same physical edge.

## 5. Excluding the regular-overlap configuration

Take an eligible C root r with cells $`X=N_0(r)`$, $`Y=N_1(r)`$ of size 16,
and two low cells of size 14. Let K be the color-1 Clebsch graph on X and L
the color-0 Clebsch graph on Y. Define

```math
F_y=N_1(y)\cap X\quad(y\in Y),\qquad
 G_x=N_0(x)\cap Y\quad(x\in X).
```

The guard **(G)** consists of

```math
\begin{aligned}
\lvert F_y\rvert=\lvert G_x\rvert&=5&&\text{for all }x\in X,\ y\in Y,\\[2pt]
d_1(x)&\geq15&&\text{for all }x\in X,\\[2pt]
d_0(y)&\geq15&&\text{for all }y\in Y.
\end{aligned}
```

These are **opposite** degree conditions. No further assumption on
$`d_0(x)`$ or $`d_1(y)`$ is part of G. H≥32 alone does not imply G.

### 5.1 Fiber centers become bijections

Each F or G fiber is an independent five-set in its respective Clebsch
graph, so uniquely write

```math
F_y=N_K(f(y)),\qquad G_x=N_L(g(x)).
```

Initially f and g are functions, not presumed permutations. Fix y, put
$`v=f(y)`$, $`Q=N_K(v)`$, and $`A=\{x\in X:c(xy)=0\}`$.
The two cross colors are disjoint, so A avoids Q. For every $`x\in Q`$,
y is in the actual opposite scope $`N_1(x)`$, and the partial-scope mask
lemma applies to its anchor $`N_K(x)`$. Thus

```math
\lvert A\cap N_K(x)\rvert\in\{2,5\}.
```

Writing $`s=|A|`$, $`h=1_{v\in A}`$, and letting a count the five-mask
occurrences over Q, the Clebsch common-neighbor count gives

**(6)**

```math
10+3a=2s+3h,\qquad 2(s-5)=3(a-h).
```

The integer a−h is even and at least −1, hence nonnegative: s≥5. All
16 rows of the cross-color-0 incidence matrix already have five entries,
so all columns also have exactly five. If $`n_t`$ is the multiplicity of
g=t, then $`Ln=5\mathbf1=L\mathbf1`$. The Clebsch identity

```math
L^2=3I-2L+2\mathbf U
```

with $`\mathbf U`$ the all-one matrix makes L nonsingular over the rationals: $`Lz=0`$ first gives
$`\mathbf1^Tz=0`$, then 3z=0. Hence every $`n_t=1`$. By symmetry f is
also bijective. At equality in (6), the pair-role index graph shows that
every pulled-back neighborhood is either an independent star-five or an
induced pentagon. Pentagons have a unique Clebsch nonneighbor.

The bijection and defect review [E30]
gives the mask argument and a full double count showing equal numbers of
pentagon rows for f and g. It also proves that zero pentagon rows is
equivalent to the corresponding map being a Clebsch isomorphism.

### 5.2 Isomorphic maps: why 3600 labels cover

If either map is an isomorphism, relabel Y by it so f=id and the two
designated Clebsch graphs coincide. Each opposite scope contains two
actual independent five-sets. Their centers are adjacent, even at scope
degree 15: each center belongs to the other five-set, so both are actual.
Their designated-color cross pattern has one full row, one full column,
and four remaining matching edges. This forces the other map g to be a
Clebsch automorphism with g(x) adjacent to x for every x.

Every Clebsch automorphism is $`x\mapsto t+\pi(x)`$, with a translation
t and a permutation of the five generators. The condition is

```math
t+\mathrm{Im}(\pi-I)\subseteq\{s_i\}.
```

No four distinct generators sum to zero, so the image has dimension at
most one. Thus π is the identity or one transposition. There are five
generator translations, and two translations for each of ten
transpositions: **25 maps**. The Lean theorem
`zero_defects_exact25_coordinates` in
[IsomorphismEndpoint.lean](formal/src/PricingG/IsomorphismEndpoint.lean)
proves this cover for the isomorphism branch under G, for all root kinds.
The retained hand review [E31] treats its U/U specialization.

Normalize the full X coloring to U or T. Retain all 72 fixed-palette Y
completions and all 25 maps, giving

**(7)**

```math
2\cdot72\cdot25=3600.
```

For every label, form the actual r+X+Y core on 33 vertices. In each of its
32 opposite scopes, filter the complete local relation by its actual
anchor cycle, role masks and known colors. If the relation is empty, that
label is impossible. If two nonempty relations force different colors for
the same physical cross edge, that label is impossible. The two-anchor
uniqueness lemma ensures at most one colored K10 prediction in the
isomorphic-map case; it does not presume a unique exterior completion.

The complete execution rejected all labels with independently checked
witnesses: **3164 empty local relations and 436 shared-edge conflicts**.
These categories record the first witness selected by the checker's scope
order; their individual counts are not invariants of the configurations.
The root-kind counts are UU: 300, UT: 1,500, TU: 300, TT: 1,500. The
cover review [E32],
literal finite contract [E33],
and terminal acceptance [E34]
separate coverage from witness checking. These are finite relation
contradictions, not SAT-solver answers.

### 5.3 Nonisomorphic maps: the shared-graph classification

Transport Y by the actual bijection g onto the physical X labels, obtaining
another Clebsch graph $`J[x,y]=L[g(x),g(y)]`$. The remaining fiber
permutation is $`p=f\circ g`$. Every J-neighborhood is either an independent
five-set or an induced five-cycle in K, with its assigned K anchor center or unique nonneighbor
identified by p. The required hand theorem is

> Either J=K, or K and J are edge-disjoint and their complement H is a
> third Clebsch graph. In the latter case the remaining fiber permutation
> p is the identity under the inherited pentagon-image rule.

Here is the structure of its proof; the detailed algebra is retained in
the shared-graph classification review [E35].
If k J-neighborhoods are pentagonal and m edges are common to K and J,
counting K-edges in J-neighborhoods gives

**(8)**

```math
5k=2(40-m).
```

Over $`\mathbb F_2`$, Clebsch adjacency squares to I. Multiplying the
pulled-back incidence matrix by K gives orthogonal columns that are unit
vectors for star rows and indicators of complementary index pentagons for
pentagon rows. Each complementary index pentagon is itself a five-set
inducing a pentagon in K. Remove
the unit columns and their occupied rows. A remaining k×k orthogonal
matrix has weight-five pentagon columns. This excludes k=1,..,7: for k≤4
there is insufficient support; k=5 repeats a column. At k=6 every
vertex-deletion would have to be C5, but the six deletions would count
30 edges while each original edge is counted four times, impossible.
At k=7 the complementary pairs would
form seven distinct pairwise-intersecting edges on seven vertices, which
is impossible. Equation (8) makes k even.

For completeness, the intermediate exclusions use even-parity
five-sign representations V,W and $`B=W^TV/4`$. Its integer entries satisfy

```math
\|B\|_{op}\leq4,\qquad \|B\|_F^2=5s,\qquad s=16-k.
```

Each independent row contributes three or five magnitude-four entries
to WB; each pentagon row contributes none. If t independent rows are
centered at their own vertex, the total is 3s+2t. Every nonzero column has
one of the following absolute shapes:

| Shape | Squared norm | Number of magnitude-four evaluations |
|---|---:|---:|
| (4) | 16 | 16 |
| (3,1) | 10 | 8 |
| (2,2) | 8 | 8 |
| (2,1,1) | 6 | 4 |
| (1,1,1,1) | 4 | 2 |
| (2) | 4 | 0 |
| (1,1) | 2 | 0 |

The evaluations over the 16 even sign rows bound the column l1 norm by
four and make it even, proving the table exhausts all possibilities.
If s>0, no column of B is zero: at an independent-type row, the
identity $`(WB)_y=V_y+3V_a`$ has every coordinate nonzero. A zero column
of B would make that coordinate zero in every row of WB.
For s=2, at least three norm-four columns are needed, exceeding total
norm ten. For s=4, count the four allowed shapes as a,b,c,d in order
(2,1,1),(1,1,1,1),(2),(1,1). The norm and column counts give d=a;
the magnitude-four count requires $`2a+b=6+t`$, whereas the column count
gives $`2a+b=5-c`$, a contradiction. For s=6 every column is (2,1,1)
and t=1. Translate the two sign representations at that unique row;
all columns are nonnegative of sum four. The operator bound forces all
row sums four. Their zero pairs cover all five coordinates, forcing that
row, all five of its J-neighbors, and a further distinct row to be
independent-type, contradicting s=6.

For k=8 the complementary binary columns are orthogonal triples. Any
triple abc forces abd, acd, bcd by row-pair parity; all remaining triples
avoid that four-set, giving two four-point blocks. Taking complements
back would make $`B\cup\{a\}`$ a K-pentagon for every a in a four-set A,
and $`A\cup\{b\}`$ a pentagon for every b in B. The graph on B is a P4;
each a joins its two endpoints, giving an endpoint four neighbors in A,
contradicting its degree two in the other pentagon.

Thus only k=0 or 16 remains. At zero, (8) gives J=K. At 16, m=0, each
J-neighborhood's unique K-nonneighbor is its own label, so p=id. The
rooted pentagon intersection numbers give the following identity, with
$`\mathbf U`$ denoting the all-one matrix and J the graph:

**(9)**

```math
KJ=\mathbf U-I+K+J.
```

It is symmetric, so K and J commute. For
$`H=\mathbf U-I-K-J`$, the Clebsch square identities give
$`H^2=5I+2K+2J`$. Hence H is the third triangle-free degree-five color
graph of a good K16 and occurs in the complete relation of Section 4.

### 5.4 Remaining G: why 10368 labels suffice and what was checked

Normalize X to U or T. Retain all 72 ordered decompositions (J,H) of the
fixed K complement and all 72 completions of the designated J color on Y:

**(10)**

```math
2\cdot72\cdot72=10368.
```

In this physical labeling, cross color 0 is J, cross color 1 is K, and the
96 cross-low edges are the 16 diagonals $`x_Xx_Y`$ and the 80 directed
copies of H edges. Opposite directed copies are distinct physical edges;
their low colors are not assumed equal.

Every opposite scope has five actual anchor vertices and five actual
pair-role vertices. In cyclic pentagon coordinates the latter have roles
$`q_i=s_{i-1}+s_{i+1}`$. Restricting the six local completions to the two
actual root colorings leaves zero, one or three full states. In the
three-state case their diagonal tuples differ from one base tuple by
flipping one of two adjacent pentagon positions. A permitted full
diagonal tuple uniquely determines the colored K10. This follows directly
from (5): a twist either changes the two fixed low edges incident with
its index, or changes none and flips that index's diagonal. The complete
diagonal proof [E36]
also treats degree 15 and retained two-state subsets after conditioning.

If no scope is empty and no diagonal is already forced incompatibly,
let R be the as-yet-unfixed diagonal coordinates. If two coordinates of
R formed an H edge, a common-J-neighbor scope would require them to be
a K-edge, a contradiction. Thus R is H-independent and has at most five
vertices by the two-color K6 bound. At most $`2^5=32`$ diagonal choices
would determine every cross-low edge, through overlapping physical
scope relations. This is a complete upper bound, not an assumption of
independence among local scopes.

The actual run needed no such branching. All **10368** labels were
rejected by **10044 empty-scope** witnesses and **324 conflicting
forced-diagonal** witnesses. An independent checker reconstructed each
named relation from the accepted reference and physical maps before
accepting its witness. No label survived.
These witness categories depend on the scope order; every label has a checked
contradiction regardless of which conflicting scope is examined first. See the
finite contract [E37]
and terminal acceptance [E38].
Together (7) and (10) therefore exclude all of G. The Lean theorem
[`GComplete.guarded_G_exclusion`](formal/src/PricingIntegration/GComplete.lean)
checks the structural reductions and finite exclusions without a native SAT
premise. The argument still requires the guards defining G; the next section
connects it to every hypothetical good host.

## 6. A global existence lemma

**Lemma.** If a good K61 satisfies (X) and the G exclusion above, it has a
C vertex r with H(r)≥32 and a neighbor p in a degree-14 root cell such
that p is high in the joining color.

Suppose no such r,p exists. A C vertex with H>32 would already have such
a p, since its two high root cells contain only 32 vertices. Hence
H≤32=w at every C vertex. By (X), H<w at A/B/D, and H≤60=w at E.
All differences w−H are nonnegative and their sum is zero by (1).
There are therefore no A/B/D vertices; every C has H=32 and every E
has H=60.

Only now is every C eligible. The assumed absence of p says that its
low-color edges have low endpoints. Equality H=32 then forces all its
high-color edges to have high endpoints. E has only high incidences,
with high endpoints by H=60. Thus both ends of every edge agree about
highness in that edge's color.

For each color i let $`L_i=\{v:d_i(v)=14\}`$. These are C vertices.
The color-i graph on $`L_i`$ is 14-regular and has no color-i edge to
its complement; the latter has degrees 15 or 16. A triangle-free graph
of minimum degree d has order at least 2d: the disjoint neighborhoods
of the two ends of any edge have at least 2d vertices. Thus any proper
nonempty $`L_i`$ has size between 28 and 31.

We need the elementary bipartiteness lemma: a triangle-free graph of
order n and minimum degree greater than $`2n/5`$ is bipartite. A
shortest odd cycle has length l≥5 and no chord. An outside vertex has
at most two neighbors on it: three cyclic gaps are each at least two,
and an odd gap of length at most l−4 would give a shorter odd cycle
through the outside vertex. Counting cycle incidences gives
$`l\delta\leq2n`$, contrary to $`\delta\gt2n/5`$.

Both low and high color-i graphs satisfy this strict bound. The
14-regular low graph has equal bipartition sizes, so $`|L_i|=28`$ or 30.
The complementary graph has at least 15 vertices on each bipartition
side and, with at most 33 vertices, only one nonempty component.

- If $`|L_i|=30`$, its high complement has sides 15 and 16. Minimum
  degree 15 makes it $`K_{15,16}`$. Exactly the 16 vertices on the
  larger side have color-i degree 15; in the C/E population these are
  precisely all E vertices.
- If $`|L_i|=28`$, its high complement has 33 vertices. Sides 15+18
  are impossible: the 18 side requires at least 270 edges, while the
  15 side permits at most 240. For sides 16+17, let their E counts be
  $`e_a,e_b`$. Edge balance gives $`256-e_a=272-e_b`$, so the counts
  are (0,16) or (1,17), and the total number of E vertices is 16 or 18.

The existence of a proper nonempty low set has therefore forced 16 or 18 E
vertices. An E vertex lies in no low set, so every other nonempty low set
is also proper and must have size 28 or 30. This justifies applying those
two size alternatives simultaneously to all four colors.

Every C belongs to two low sets. If there are 18 E vertices, the sum of
the four low-set sizes is 86; no size 30 is possible, and 86 is not a
multiple of 28. If there are 16 E vertices, the sum is 90, forcing sizes
30,30,30,0. In each of the first three colors all 16 E vertices are in
one independent part of $`K_{15,16}`$, so every edge between them has
the fourth color. That produces a monochromatic triangle. Thus no
proper nonempty $`L_i`$ exists.

If all $`L_i`$ are empty, every vertex is E; a color graph would be
15-regular on 61 vertices, contradicting the handshake lemma. Otherwise
one $`L_i`$ is the whole vertex set, so all vertices are C. As every
low set is empty or full, they all share one pair of low colors and
one pair of high colors. At any root, the attaching degree-16
neighborhood of $`x\in X`$ in color 0 is the root plus intersections
with Y and the two low cells. Each intersection has size at most five;
all three must be five. Symmetrically all other fibers in G are five,
and all opposite degrees are 16. This is exactly G, already excluded.
The contradiction proves the lemma.

The bridge [E39] and
independent hand review [E40]
record this proof. Its C/E-only and synchronized conclusions hold inside
the *temporary no-entrance contradiction*. They must not be inserted
as constraints into the formulas searched after an entrance exists.

## 7. Three actual neighborhoods at the remaining root

Normalize the lemma's root to $`X=N_0(r),Y=N_1(r),P=N_2(r),Q=N_3(r)`$,
of sizes 16,16,14,14, and put p in P by a single global low-color swap.
Let $`S=N_2(p)`$. It contains r, meets neither P nor p, and decomposes
as

```math
S=\{r\}\mathbin{\dot\cup}A\mathbin{\dot\cup}B
                  \mathbin{\dot\cup}D,
 \quad A=X\cap S,\ B=Y\cap S,\ D=Q\cap S.
```

Each intersection is a good two-colored clique of size at most five.
Since p is high, S has order 15 or 16. The sizes are 555 or a permutation
of 455. If A is short, globally swap the equal high colors and X,Y.
The remaining shapes are **555,554,545**.

The complete X and Y are actual K16s. S is actual K16 or actual K15
with its one formal completion position. A has five actual vertices,
so that missing position, if any, lies among the five reference
positions of the indicated short B or D cell.

In X, A is independent in actual color 2, hence a Clebsch neighborhood.
In S, it is the actual color 0 neighborhood of r. The same A cycle uses
actual colors 1 and 3 in both. Choose its physical colored-cycle labeling
once and use it for both coordinate systems. Their six anchored states
are subjected to the **same** order-ten dihedral action. There are six
pair orbits, of sizes 1,5,5,5,10,10. Every omitted-position choice is
retained *after* taking that simultaneous quotient.

The complete Y template must then be bound to the actual B:

- For $`\lvert B\rvert=5`$, its colored cycle fixes an anchor; retain all six
  compatible Y completions.
- For $`\lvert B\rvert=4`$, its two colors are P4s because it is a deletion from
  the B cell of the S completion. As an independent four-set in Y's
  color 2 Clebsch graph, it may be a star-four or a nonstar-four.
  In the star case, the unique fifth Y anchor vertex is actual and
  outside S. It is explicitly a color 2 nonneighbor of p. It is not
  S's formal missing position.
- In the nonstar case, the affine-plane translations and permutations
  of its three nonzero directions induce all 24 permutations of its
  four points, each extending to the whole designated Clebsch graph.
  Normalize the actual P4 to reference order (0,3,5,6). The complete
  relation has two matching Y states; retain both. Transporting
  other colors under that graph automorphism must still land in
  the complete 72-state relation, rather than pretending the map
  preserves every three-color completion.

The unassigned Y vertices can be mapped bijectively to unused actual Y
positions, with no omitted injection factor. X/S agree on A and S/Y on B; all remaining domains are
disjoint. These maps extend to one bijection of all 61 actual vertices.
The anchor-geometry explanation [E41]
and its review [E42]
make the star/nonstar and physical/formal distinctions explicit.

## 8. The exhaustive 456-case cover

The resulting conservative cover is

| Shape and Y anchor | X/S pair orbits | Missing-position choices | Y states | Cases |
|---|---:|---:|---:|---:|
| 555, five-anchor | 6 | 1 | 6 | 36 |
| 554, five-anchor | 6 | 5 | 6 | 180 |
| 545, star-four | 6 | 5 | 6 | 180 |
| 545, nonstar-four | 6 | 5 | 2 | 60 |
| **Total** | | | | **456** |

These labels form a cover; they need not form a disjoint partition of
physical colorings.
The seed generator [E43] records
reference-state indices, simultaneous pair orbits, omitted coordinates,
full physical maps, and signed units. The
independent seed/clause audit [E44]
checks the actual exhaustive choices; the generator's own count assertion
does not establish completeness by itself.

Physical labels are r=0, X=1..16, Y=17..32, P=33..46, Q=47..60,
p=33. Reference palettes (designated Clebsch color, positive sign,
negative sign) are X:(2,1,3), S:(0,1,3), Y:(2,0,3). These are bindings
to one physical palette, not independent recolorings. A null S reference
slot contributes no vertex or edge. Each seed fixes actual X,Y,S
template colors, every color 2 edge from p to S, and color 2
nonmembership for every other actual vertex except p itself.

For each label the corresponding formula is
BROAD_BASE_001.cnf [E45]
plus the signed units for one row of
SEEDS.json [E46].
The base has **439723 declared variables and 1880888 clauses** before
seed units. It retains all 61 vertices and all 1830 physical edges.
Its physical clauses include exactly-one color per edge and the four
triangle prohibitions for each of $`\binom{61}{3}=35990`$ triangles, plus
60 unit clauses fixing the root spokes to their specified colors.
The interiors of both K14 cells and every exterior edge remain present.

The remaining variables are explicit counters and indicators. For an
ordered input list $`b_1,\ldots,b_m`$, assign threshold $`T(i,k)`$ the
truth value “at least k of the first i inputs are true.” The four-clause
recurrence encodes

```math
T(i,k)\leftrightarrow T(i-1,k)\lor(b_i\land T(i-1,k-1))
```

with its true k=0 and false i=0,k>0 boundaries. This assignment satisfies
all degree, H and retained fiber definitions for any actual coloring.
The per-incidence high bit selects the *neighbor's* degree in the
actual joining color. The H counters stop at threshold 48, which does
not cap H: a larger value makes every retained threshold true.

These constraints enforce degree≤16, all 35 exact profile choices,
the supplied C root and H(r)≥32, and (X) at every A/B/D vertex. The
root-entrance lemma and the A/B/D results justify these conditions.
Assign all physical color variables from the relabeled hypothetical
host and all counters their actual prefix counts; this constructs a
satisfying assignment of its corresponding formula.

The formulas impose neither the opposite-high conditions from G nor a
small-fiber restriction. Their 7,456 fiber-counter clauses define auxiliaries
without restricting the fibers. All physical clauses and auxiliary definitions
are checked in the parent-base semantic audit [E44]; the broad-input audit
[E47] verifies that deleting exactly 32 opposite-degree units and one
small-fiber disjunction leaves every other clause unchanged. The retained
`REGIME_3` and `R3_*` seed labels are identifiers from that parent encoding;
the final formulas use `BROAD_BASE_001.cnf`, with those 33 restrictions removed.
No C/E-only, synchronized-highness, maximum-H, H≥33 or K14 extension assumption
is used. The host-to-CNF review [E48] details the satisfying assignment and its
premises.

## 9. Completion of the argument

Assume a good K61. Sections 2–3, with the accepted exact A/B/D native
refutations, give (X) at every vertex. Sections 4–5 supply the complete
guarded G exclusion. Section 6 then gives an eligible C root and an
actual exterior high endpoint in the same coloring. Sections 7–8 map
that coloring to a satisfying assignment of one of the 456 exact
full-host formulas.

The C reconciliation [E49] records matching native UNSAT answers from
Kissat and CaDiCaL for every one of these 456 formulas, with both answers
bound to the same complete formula hash. These refutations contradict the
satisfying assignment supplied by the cover.

Consequently no good coloring of K61 exists. This establishes
$`R(3,3,3,3)\leq61`$ and completes the computer-assisted proof.

There is no subsequent search for an exterior completion: the final formulas
already contain every host edge. The regular-overlap configuration and the
456-case family are connected by the global existence lemma, not by adding
their case counts. The dependency order is acyclic:

> smaller-order structure → supplied-root exclusions → incidence bounds (X)
> → the global existence lemma using the separate G exclusion → the physical
> 456-case cover → the exact formula contradiction.

The G exclusion depends on the critical-neighborhood structure and its own
finite witnesses, not on the 456 native answers. ∎

## 10. Verification and reproducibility

The written argument and the Lean development establish the mathematical
reduction: every hypothetical good coloring reaches an exhaustive finite case
and supplies a satisfying assignment of its explicit formula. The finite G
compatibility exclusions are proved within this reduction. Native SAT runs
supply the unsatisfiability assertions for the 56,830 formulas.

The publication presents a complete computer-assisted proof at the native-SAT
trust standard. The supplied sources, exact inputs and result records support
independent audit and fresh solver runs.

| Component | Evidence supplied |
|---|---|
| Mathematical reductions | The written argument and complete Lean proofs of physical extraction, exhaustive coverage, transport and encoding soundness |
| Critical K15/K16 structure | Local Lean completeness proofs, explicit templates, 55 small CNF/LRAT pairs and an actual-host adapter consumed by the reduction |
| Finite G exclusions | Kernel-checked structural and finite-cover arguments; independent reconstruction of the 3,600 and 10,368 compatibility checks |
| Exact SAT input binding | Complete Lean-emitted formula comparisons with retained or reconstructed DIMACS headers, ordered clauses and signed suffixes, plus runner-recorded formula hashes |
| SAT computation | Exhaustive case censuses and matching Kissat/CaDiCaL UNSAT records for every one of the 56,830 formulas |

### The formal theorem and its computational premise

The endpoint is
[`PricingIntegration.NativeWholeProof.ramsey61`](formal/src/PricingIntegration/NativeWholeProof.lean):

```lean
ramsey61 (h : AllNativeUnsat) : ∀ c : Host, ¬NoMonochromaticTriangle c
```

`Host` is a coloring of the actual 61 vertices. `AllNativeUnsat` ranges over
an explicit finite type of concrete CNFs: 55,016 common A/B/mixed-D cases,
1,358 UUU/UUT cases and 456 C cases. Their total, 56,830, is
[proved in Lean](formal/src/PricingIntegration/NativeWholeCount.lean).
All mathematical coverage, physical transport and encoding implications are
proved and supplied to the endpoint. Its only computational premise is the
unsatisfiability of those formulas.

The native results are external evidence for that premise; the endpoint does
not check the large SAT refutations in Lean. Exact DIMACS byte and hash
comparisons also use external verification tools, described in
[the formula-binding guide](formal/reproduce/README.md). Many retained native
logs contain only the quiet-mode UNSAT status; commands, input hashes and
resource records are supplied by the runners. All original inputs are
reproducible, and [E50] records the original input/result accounting. The
[A/B/D second-solver receipt](publication/checks/ABD_SECOND_SOLVER.json)
records the complete CaDiCaL rerun, with no SAT, UNKNOWN or error results.

The [complete portable source build](formal/BUILD_RESULT.json) compiled all
1,809 modules from a fresh checkout, including all 32 classification modules
and replay of their 55 small CNF/LRAT pairs. No prior project artifacts were
reused. Its scope, the final theorem interface and the check records are
documented in
[FORMALIZATION_STATUS.md](publication/FORMALIZATION_STATUS.md),
[TRUST_AND_CERTIFICATION.md](publication/TRUST_AND_CERTIFICATION.md) and
[RELEASE_CHECKS.md](publication/RELEASE_CHECKS.md).

**Independent human verification remains outstanding.** The human author
has not independently verified the complete mathematics and computations.
The research, implementation and formalization were heavily assisted by AI.
The author is responsible for the claim, its supporting artifacts and any
corrections. The supplied argument, code and evidence
make the result available for that review and for reproduction from the
original formulas.

## Sources and attribution

The local critical-neighborhood development is supplied in
[`classification/`](classification/) with its source and certificate manifest.
The historical classification attribution is discussed in
[classification provenance](publication/CLASSIFICATION_PROVENANCE.md).

The project's research reports, mathematical reviews, finite checking sources
and native result records are indexed below and in
[DEPENDENCIES.json](publication/DEPENDENCIES.json). Many reduction proposals
originated in GPT-6 Pro reports. Research contributions are recorded in
[ATTRIBUTION.md](publication/ATTRIBUTION.md).

## Appendix A. Portable evidence locators

The proof is readable without a local filesystem layout. To inspect its
underlying finite data or native records, authenticate and extract
`archives/evidence-v1.tar.gz` using the
[reproducibility instructions](publication/REPRODUCIBILITY.md).
Every path below is relative to the root of that extraction, not to a
GitHub URL. These code-formatted locators avoid links to files that are
present only in the downloadable evidence. Absolute paths inside historical
records identify original provenance and are not requirements on a reader's
machine.

The locators name the specific source or evidence used by the argument;
locating or hashing a file does not itself validate its mathematics. Exact
pins and the direction of each dependency are in the dependency ledger.
The [A/B/D evidence index](publication/ABD_EVIDENCE_INDEX.md) additionally
lists the complete family manifests, support/matrix data, base formulas and
case censuses consumed by the portable reconstruction tools. The
[D cover specification](publication/D_COVER_AND_ENCODING.md) connects those
data to the physical reductions in §3.

| Reference | Archive-relative path |
|---|---|
| [E1] | `mathematics/retained/CLASSIFICATION_SOURCES.md` |
| [E2] | `support/workspace/R4333Lean/CriticalCatalogues.lean` |
| [E3] | `support/workspace/R4333Lean/K15Catalogue.lean` |
| [E4] | `mathematics/retained/LITERAL_U_T_MATRICES.json` |
| [E5] | `support/workspace/R4333Lean/CriticalTemplatePaletteSymmetry.lean` |
| [E6] | `support/workspace/R4333Lean/CriticalTemplateDeletion.lean` |
| [E7] | `evidence/c_campaign/FINAL_COMPOSITION_MATH_REVIEW_001.md` |
| [E8] | `support/workspace/r4333_upper/pro_findings_review_2026_09_11/ramsey61_research/marked_catalogue.py` |
| [E9] | `evidence/A/SELECTED_A_HAND_COVERAGE_DESIGN_000.md` |
| [E10] | `evidence/A/INDEPENDENT_A_INPUT_SPEC_AND_EXTRACTION_000.md` |
| [E11] | `evidence/A/INDEPENDENT_SELECTED_A_ACTUAL_FINITE_REVIEW_000.json` |
| [E12] | `evidence/A/INPUT_EXECUTION_ACCEPTANCE_000.json` |
| [E13] | `evidence/B/INDEPENDENT_SELECTED_B_HAND_COVERAGE_REVIEW_000.json` |
| [E14] | `evidence/B/tools/SELECTED_B_INPUT_SPEC_000.md` |
| [E15] | `evidence/B/INDEPENDENT_SELECTED_B_ACTUAL_FINITE_REVIEW_000.json` |
| [E16] | `evidence/B/INDEPENDENT_SELECTED_B_ACTUAL_INPUT_REVIEW_000.json` |
| [E17] | `evidence/D/UUT/ORIGINAL_UUT_679_HAND_COVERAGE_CLAIM_000.md` |
| [E18] | `evidence/D/UUT/ORIGINAL_UUT_679_INDEPENDENT_REVIEW_000.md` |
| [E19] | `evidence/D/mixed/UTU_UTT_ORIGINAL_FINITE_BOUNDARY_DESIGN_000.md` |
| [E20] | `evidence/D/mixed/TT_SUPPORT_PAIR_PRECLASSIFICATION_REDUCTION_000.md` |
| [E21] | `evidence/D/mixed/INDEPENDENT_MIXED_D_FINITE_DATA_REVIEW_000.json` |
| [E22] | `evidence/D/mixed/INDEPENDENT_MIXED_D_COMPLETE_INPUT_DEFINITIONS_REVIEW_000.json` |
| [E23] | `evidence/c_campaign/ABD_SELECTOR_INTERFACE_AUDIT_001.md` |
| [E24] | `evidence/c_campaign/ABD_SELECTOR_INTERFACE_AUDIT_001.json` |
| [E25] | `support/workspace/research_handoffs/ramsey61_density_20260912_001/D_UUU_FULL_HOST_REUSE_CLAIM_000.md` |
| [E26] | `mathematics/retained/LOCAL_72_STATE_HAND_REVIEW.md` |
| [E27] | `mathematics/retained/ACCEPTED_72_STATE_REFERENCE.json` |
| [E28] | `mathematics/retained/ACCEPTED_72_STATE_SUMMARY.json` |
| [E29] | `mathematics/retained/PARTIAL_SCOPE_REVIEW.md` |
| [E30] | `mathematics/retained/G_BIJECTION_REVIEW.md` |
| [E31] | `evidence/G/retained/g_isomorphism/context/GUARDED_UU_EXCLUSION_REVIEW_000.md` |
| [E32] | `evidence/G/retained/g_isomorphism/context/COVER_JOIN_AND_SCOPE_REVIEW_000.md` |
| [E33] | `evidence/G/retained/g_isomorphism/IMPLEMENTATION_CONTRACT.md` |
| [E34] | `mathematics/retained/G_ISOMORPHIC_FINITE_ACCEPTANCE.md` |
| [E35] | `mathematics/retained/G_SHARED_GRAPH_CLASSIFICATION_REVIEW.md` |
| [E36] | `evidence/G/retained/g_remaining/context/DIAGONAL_REDUCTION_AND_COVER_REVIEW.md` |
| [E37] | `evidence/G/retained/g_remaining/IMPLEMENTATION_CONTRACT.md` |
| [E38] | `mathematics/retained/G_REMAINING_FINITE_ACCEPTANCE.md` |
| [E39] | `evidence/c_campaign/BROAD_456_WHOLE_C_BRIDGE_001.md` |
| [E40] | `evidence/c_campaign/BROAD_BRIDGE_INDEPENDENT_REVIEW_001.md` |
| [E41] | `evidence/c_campaign/ANCHOR_GEOMETRY_EXPLANATION_001.md` |
| [E42] | `evidence/c_campaign/ANCHOR_GEOMETRY_REVIEW_001.md` |
| [E43] | `evidence/c_campaign/tools/seeds.py` |
| [E44] | `evidence/c_campaign/reviews/INDEPENDENT_AUDIT_001.json` |
| [E45] | `evidence/c_campaign/inputs/BROAD_BASE_001.cnf` |
| [E46] | `evidence/c_campaign/inputs/SEEDS.json` |
| [E47] | `evidence/c_campaign/reviews/BROAD_INPUT_AUDIT_001.json` |
| [E48] | `evidence/c_campaign/FINAL_ENCODING_COVER_REVIEW_001.md` |
| [E49] | `evidence/c_campaign/reviews/BROAD_SECOND_TAIL_RECONCILIATION_001.json` |
| [E50] | `evidence/final_validation/FINAL_OUTCOME_002.json` |
