# An improved upper bound for the Ramsey number R(3,3,3,3)

## The result and the proof route

**Theorem.** Every four-coloring of the edges of the complete graph on 60
vertices contains a monochromatic triangle. Consequently,

```math
R(3,3,3,3)\leq60.
```

Call an edge coloring **good** if it contains no monochromatic triangle.
The proof assumes a good coloring of one complete graph on 60 vertices and
derives a contradiction. Combinatorial arguments reduce this hypothetical
coloring to an exhaustive family of Boolean formulas. Every formula describes
the same 60 physical vertices; overlapping neighborhoods share their actual
edge colors.

The finite boundary has **296,797 cases**: 287,542 marked A/B/D/E cases,
8,532 entrance cases, three all-five cases and 720 mixed marked-balance
cases. The mathematical reductions, finite coverage arguments, and implications
from a host coloring to these formulas are formalized in Lean. Unsatisfiability
of the exact formulas is the external computational premise, checked with
Kissat. The precise division between the Lean proof and native computations
is given in [Section 9](#9-formal-theorem-and-computational-boundary).

The argument has three parts. First, double counting tickets converts
local bounds for A, B, D and E into a choice between an entrance at C1 or
C2 and perfect balance. The same marked-neighborhood construction excludes
the entrances. In perfect balance, reciprocity and two applications of
neighborhood homogeneity force a common critical pair. Three auxiliary
exclusions then supply a C2 root. A marked brace at that root, together
with the visible-neighborhood compatibility conditions, gives one of the
720 remaining formulas.

Throughout, an **actual** vertex belongs to the hypothetical host graph. A
**reference position** is a coordinate in a template. In particular, the
missing position used to describe a 15-vertex neighborhood is never treated
as an additional host vertex. All vertex permutations act on the complete
host, and every color permutation is global. Template coordinate maps may
differ between neighborhoods, but they never change the colors of shared
physical edges independently.

## 1. Neighborhoods, templates and profiles

Use colors 0, 1, 2 and 3. For a vertex v, put

```math
N_i(v)=\{u\ne v:c(uv)=i\},\qquad d_i(v)=|N_i(v)|.
```

No edge inside N_i(v) has color i, since it would form a monochromatic
triangle with v. Thus each N_i(v) is a good three-colored complete graph.
The bounds R(3,3)=6 and R(3,3,3)=17 give

```math
11\leq d_i(v)\leq16,\qquad \sum_{i=0}^{3}d_i(v)=59.
```

We call color i **critical** at v when d_i(v) is 15 or 16, and call N_i(v)
a **critical neighborhood**. The proof uses the following classification:
up to vertex relabeling and color permutation, there are exactly two good
three-colorings of K16, denoted U and T, and every good three-coloring of K15
is obtained by deleting one vertex from U or T. The supplied Lean development
proves these classification statements using 55 checked CNF/LRAT pairs.

For an explicit description, identify the template positions with the
integers 0 through 15 under bitwise exclusive or, written +. Let

```math
\Delta_0=\{1,8,10,12,15\},\quad
\Delta_1=\{2,3,7,11,13\},\quad
\Delta_2=\{4,5,6,9,14\}.
```

In U the edge xy has color j when x+y belongs to Delta_j. The template T is
obtained by interchanging colors 1 and 2 on the 16 edges between
{1,2,8,11} and {5,6,12,15}. Write U-minus and T-minus for the restrictions
to positions 0 through 14. The literal definitions are in
[CriticalTemplates.lean](formal/src/R4333Lean/CriticalTemplates.lean).

The finite template checks establish that the color-preserving automorphism
groups of U and T have orders 160 and 32 and act transitively on vertices.
Their point stabilizers have orders 10 and 2. They also establish that every
permutation of the three template colors can be realized by a vertex
permutation fixing a specified reference position. For a deleted template,
the color-preserving automorphisms are exactly those of its full template
fixing the missing position.

These facts allow a fixed palette convention. On N_i(v), template colors
0,1,2 mean the other three host colors in increasing order. A classification
map with a different palette is corrected by a template vertex map, without
recoloring physical edges. For order 15, the missing position is 15 and the
palette correction fixes it. For order 16, a chosen actual vertex may be
placed at position 15.

The four deficits 16-d_i(v) are nonnegative and sum to five. Their partitions
give exactly six sorted degree profiles:

| Profile | Sorted degrees | Critical neighborhoods | Tickets sent, w(v) |
|---|---|---:|---:|
| A | (11,16,16,16) | 3 | 48 |
| B | (12,15,16,16) | 3 | 47 |
| C1 | (13,14,16,16) | 2 | 32 |
| D | (13,15,15,16) | 3 | 46 |
| C2 | (14,14,15,16) | 2 | 31 |
| E | (14,15,15,15) | 3 | 45 |

## 2. Tickets and the global alternative

A vertex u **sends a ticket** to a different vertex v if the color of uv is
critical at u. Equivalently, the actual neighborhood N_c(uv)(u) contains v
and has order 15 or 16. Define the numbers received and sent by

```math
H(v)=|\{u\ne v:d_{c(uv)}(u)\geq15\}|,
\qquad
w(v)=\sum_{i:d_i(v)\geq15}d_i(v).
```

Double counting the tickets, once at the sender and once at the receiver, gives

```math
\sum_v H(v)=\sum_v w(v).
```

The marked case cover in Section 4 proves the strict bounds

```math
\begin{array}{c|cccc}
\text{profile}&A&B&D&E\\
\hline
H(v)&\leq47&\leq46&\leq45&\leq44.
\end{array}
```

An **entrance** is a pair (r,p) where r has profile C1 or C2, p belongs
to a noncritical neighborhood of r, and p sends r a ticket. If there is no
entrance, a C1 or C2 vertex receives tickets only from its two critical
neighborhoods, so H(v) is at most w(v).

Together with the A/B/D/E bounds this gives H(v) at most w(v) everywhere.
The differences w(v)-H(v) are nonnegative integers with sum zero, so each
is zero. The strict-deficit profiles A, B, D and E cannot occur. Every C1
or C2 vertex receives a ticket from every neighbor in its critical colors,
and from no other neighbor.

Call a good coloring **perfectly balanced** if it has no entrance and
H(v)=w(v) everywhere. We have proved the following alternative, subject
only to the A/B/D/E exclusions: either an entrance exists, or the host is
perfectly balanced and has only profiles C1 and C2. Section 5 excludes the
first possibility; Sections 6 and 7 exclude the second.

## 3. One physical encoding and a common marked construction

### 3.1 The full-host base

For every unordered edge e of K60 and every color i, use a Boolean variable
x_(e,i) asserting that e has color i. There are

```math
4\binom{60}{2}=7,080
```

physical variables. The common base contains one at-least-one-color clause
and six pairwise at-most-one-color clauses for each edge, and one
monochromatic-triangle prohibition for each triangle and each color:

```math
\bigvee_{i=0}^{3}x_{e,i},\qquad
\neg x_{e,i}\vee\neg x_{e,j}\quad(i<j),
```

```math
\neg x_{uv,i}\vee\neg x_{uw,i}\vee\neg x_{vw,i}.
```

This gives

```math
7\binom{60}{2}+4\binom{60}{3}=149,270
```

base clauses. Its satisfying assignments correspond exactly to good
four-colorings of K60.

A **marked case** adds only signed physical edge facts to this base.
A positive fact fixes an edge color; a negative fact excludes that color.
It is encoded by the corresponding unit clause. Repeated facts do not
change satisfiability, and the binding checks retain the exact ordered
unit lists used to generate the inputs. All A/B/D/E and entrance cases have
7,080 variables. The balance cases use this same physical base with
the additional constraints described in Section 7.4.

### 3.2 Extracting the mark and its supports

Choose a root r and write R_i=N_i(r). Suppose R1 and R2 have placed
critical templates. Call them the **foreign cells**. Let p belong to R3
and suppose p sends a ticket to r, so d3(p) is 15 or 16. The vertex p is
the **mark**; its actual critical neighborhood

```math
S=N_3(p)
```

is the **brace**. Its three supports are S_i=S intersect R_i for i=0,1,2.
No template is assumed on the **free cell** R0. A template on R3 may be
present, but is not required by this construction.

The root is in S. No other vertex of R3 is in S, because it would form a
color-3 triangle with r and p. Therefore

```math
S=\{r\}\mathbin{\dot\cup}S_0\mathbin{\dot\cup}S_1
\mathbin{\dot\cup}S_2.
```

Inside S_i, colors i and 3 are forbidden. Each support is a good two-colored
clique and has at most five vertices. Since their total size is 14 or 15,
the ordered support sizes, or **shapes**, are exactly

```math
(4,5,5),\quad(5,4,5),\quad(5,5,4),\quad(5,5,5).
```

The internal support colorings are more specific than arbitrary good
two-colorings. Classification applies to the actual brace S. Each color
degree in a good three-colored K16 is five: it is at most five by R(3,3)=6,
and the three degrees sum to fifteen. Its color neighborhoods are therefore
two complementary five-cycles. Deleting one reference position removes at
most one vertex from one of those neighborhoods. Consequently a five-support
has complementary five-cycles, and a four-support has complementary
four-vertex paths. The path conclusion uses critical classification.

### 3.3 Finite words and whole-cell symmetries

Fix reference colorings for these paths and cycles. A support labeling is
a color-preserving bijection from its reference coloring onto the support.
For a support shape, list both brace templates U and T, or their one-vertex
deletions. The base vertex represents r and must have the specified number
of neighbors in each color. For order 16, transitivity permits it to be
fixed at position 15. For order 15, include every eligible base vertex.
In either case, enumerate every color-preserving labeling of its three
neighbor sets, with two choices for a path and ten for a cycle.

Read the edge colors between the three ordered supports. This produces a
**word** with 65 entries for a shape containing a four-support, or 75 entries
for shape (5,5,5). Exhaustive finite enumeration gives exactly 600 distinct
words for each shape: 100 from U or U-minus, and 500 from T or T-minus.
They are labeled color arrays. Their exhaustiveness follows by applying
classification to the actual brace and composing the actual support
orders with its template map.

For each foreign cell, enumerate all subsets carrying the required colored
path or cycle, and choose one subset in each orbit under color-preserving
automorphisms of the **whole foreign template**. Call these the **selected
supports**, each with a fixed reference labeling. Put the free support on
fixed vertices of R0 in reference order.
For fixed root-cell sizes and template types, a selected support pair
together with any of the 600 words is a **normalized configuration**.
The free path or cycle automorphisms, of orders 2 or 10, and the
whole-template set stabilizers of the foreign supports act on its words.
They allow reduction to orbit representatives.

Each normalized configuration records:

1. All 59 root edges, according to their root cells.
2. Every edge in the two foreign templates, and in the marked cell if a
   template there is supplied.
3. The internal free-support coloring and the cross-support word.
4. For every vertex v other than p, the exact equivalence
   c(pv)=3 if and only if v belongs to the root together with the three
   selected supports.

The fourth item includes negative membership on every vertex outside the
brace except the mark. The positive root-mark fact is already
among the root edges. Each physical edge has one identity throughout.

Write F(K) for the signed facts of a case or normalized configuration K.
A symmetry uses one permutation sigma of all 60 vertices and one global
color permutation tau, with

```math
c'(\sigma(u)\sigma(v))=\tau(c(uv)).
```

Represent a fact by (uv,i,+) for equality to color i, or (uv,i,-) for
inequality. Its **pullback** preserves the sign and is

```math
(uv,i,\varepsilon)\longmapsto
(\sigma^{-1}(u)\sigma^{-1}(v),\tau^{-1}(i),\varepsilon).
```

A retained list satisfies the **finite coverage condition** if, for every
normalized configuration N, some retained case K and symmetry satisfy

```math
(\sigma,\tau)^*F(K)\subseteq F(N).
```

Thus every target fact holds in the transformed coloring whenever the
source facts hold. This condition includes all positive and negative
membership facts. Word-orbit reductions and exchanges of equal-sized
cells provide covering symmetries under this same criterion.

**Coverage proof.** By Section 3.2, each actual support admits its reference
coloring. Normalize the foreign supports using automorphisms of their
entire templates. Send the free support, in reference order, to its fixed
positions, and extend this bijection to a permutation of the whole free
cell. These maps fix r and R3 and combine into one permutation of all 60
vertices. They preserve the root edges, foreign templates and any supplied
marked template, and give the free support its reference coloring.

Because p is fixed, its brace becomes exactly the root and the selected
supports, preserving both positive and negative membership. A template
isomorphism of this brace sends r to an eligible base vertex. Under that
map, the fixed support labelings become color-preserving labelings of its
three neighbor sets, so the resulting cross word belongs to the enumerated
600. All facts of a normalized configuration therefore hold.

Apply the symmetry supplied by the finite coverage condition. Every
retained-case fact holds because its pullback belongs to this
configuration. Goodness is preserved by the same symmetry. No template
on R3 is required, and the free cell need not extend to a critical coloring.

## 4. The A, B, D and E ticket bounds

Suppose a root violates its proposed bound. Its incoming ticket count is
at least 48, 47, 46 or 45 in profiles A, B, D or E. Name its groups
R0 through R3 in increasing order of size, ordering the template types
by U<T among critical groups of equal size. Every group exchange uses one
global permutation of its root colors followed by fixed-palette normalization.

Only 59-|R3| neighbors lie outside R3. Consequently R3 contains at least
five, four, three or one ticket senders, respectively. Choose one as the
mark p. The two foreign cells R1 and R2 are critical, so Section 3 applies.

In the marked template, retain one position from each vertex orbit for p.
Transitivity gives one choice in U or T, placed at reference position 15;
there are three choices in U-minus and nine in T-minus. The marked group
contains no support, so its normalization preserves the support and word facts.

When both foreign groups have size 15, also exchange R1,R2 and colors 1,2.
Restore the template palettes and the free support's reference coloring,
and move the mark to a retained orbit representative. When the foreign types
agree, this identifies shapes (5,4,5) and (5,5,4). For two foreign T types
and shapes (4,5,5) or (5,5,5), order the two five-support orbits; if they
coincide, make no further exchange reduction.

The following counts include all mark positions. A row with marked types
U,T is used once for each listed type. A dash means that foreign-group
exchange covers shape (5,5,4) through shape (5,4,5). A three-letter family
name lists the types of R1, R2, R3 in that order.

| Profile | Foreign | Marked | (4,5,5) | (5,4,5) | (5,5,4) | (5,5,5) | Cases per listed marked type |
|---|---|---|---:|---:|---:|---:|---:|
| A | UU | U,T | 4 | 4 | 4 | 2 | 14 |
| A | UT | T | 16 | 16 | 20 | 4 | 56 |
| A | TT | T | 76 | 92 | 92 | 16 | 276 |
| B | UU | U,T | 36 | 40 | 36 | 10 | 122 |
| B | UT | T | 168 | 184 | 204 | 36 | 592 |
| B | TU | U,T | 168 | 220 | 168 | 36 | 592 |
| B | TT | T | 828 | 1,084 | 996 | 168 | 3,076 |
| D | UU | U,T | 189 | 408 | — | 82 | 679 |
| D | UT | U,T | 1,824 | 1,992 | 2,388 | 372 | 6,576 |
| D | TT | U,T | 5,256 | 11,892 | — | 1,056 | 18,204 |
| E | UU | U | 567 | 1,224 | — | 246 | 2,037 |
| E | UU | T | 1,701 | 3,672 | — | 738 | 6,111 |
| E | UT | T | 16,416 | 17,928 | 21,492 | 3,348 | 59,184 |
| E | TT | T | 47,304 | 107,028 | — | 9,504 | 163,836 |

For every row, the finite checks and transport proofs establish the coverage
condition of Section 3.3 on every normalized support pair and its 600 words.
Each target includes the complete root and supplied template facts,
free-support pattern, cross word and signed brace membership.

### Excluding the selected roots

The family totals are 360 A, 5,096 B, 50,918 D and 231,168 E cases.
Every selected root supplies an actual mark, and the covers just proved
send its host to one of these **287,542 cases**. The physical coloring would
satisfy the corresponding base and units. Unsatisfiability of every case
therefore proves H at most 47, 46, 45 and 44 for A, B, D and E. These are
ticket bounds; they do not assert that an isolated root of one of these
profiles is impossible without the global counting argument.

## 5. Excluding C1 and C2 entrances

An entrance supplies a root r and a mark p in a noncritical group. Name that
group R3, the other noncritical group R0, and the two critical groups R1,R2.
Place templates only on R1 and R2. The common construction applies to the
actual brace N3(p), with no template on either low group.

First consider reference patterns with two foreign 16-vertex templates,
ordered as UU, UT or TT. Their support and word actions are those of the
A rows with no marked template. The untemplated group complements have
only root edges and negative brace membership specified, so their sizes
do not change the actions. This gives 346 reference patterns.

For C1 both foreign groups have size 16. The marked noncritical group may
have size 13 or 14, giving two assignments of the low group sizes and two
formulas per reference pattern.

For C2, complete the 15-vertex foreign template by its missing reference
position outside the support. Normalizing and ordering the two foreign
templates may exchange them, so the missing position can occur in either.
Delete a position outside the support: two five-supports give 11+11=22
choices, and a four-support and a five-support give 12+11=23 choices.
This is a local template description, with no assumption that the good
host extends to a larger complete graph.

| Foreign types / cases | (4,5,5) | (5,4,5) | (5,5,4) | (5,5,5) | Total |
|---|---:|---:|---:|---:|---:|
| UU patterns | 4 | 4 | 4 | 2 | 14 |
| UT patterns | 16 | 16 | 20 | 4 | 56 |
| TT patterns | 76 | 92 | 92 | 16 | 276 |
| **Reference patterns** | **96** | **112** | **116** | **22** | **346** |
| **C1 formulas** | **192** | **224** | **232** | **44** | **692** |
| **C2 formulas** | **2,112** | **2,576** | **2,668** | **484** | **7,840** |

**Coverage proof.** The actual brace gives its support colorings and one of
the 600 words. For C1 the marked-neighborhood cover applies directly in
either low-group assignment. For C2 normalize the completed foreign template
and apply the finite support-and-word cover, retaining the image of the
missing position. All its possible images are included. Delete that image
and its incident facts. Every remaining positive or negative fact pulls
back to a true fact on an actual edge.

The support maps extend over their group complements, preserving signed
membership. Thus every entrance yields a satisfying assignment to one of
these **8,532 exact formulas**. Since all are unsatisfiable, no entrance exists.

## 6. Perfect balance forces a common critical pair

Assume perfect balance. Section 2 leaves only C1 and C2, with every possible
incoming ticket in the indicated critical groups present.

### 6.1 Reciprocity and internal connectivity

**Reciprocity.** An edge's color is critical at one endpoint if and only if
it is critical at the other. If u sends v a ticket, the absence of an
entrance at v makes that edge color critical there, so v sends a ticket back.

**Internal connectivity.** Every single-color graph in a good
three-coloring of K_n, for n=15 or 16, is connected. Every color degree
is at most five, because its neighborhood is a good two-colored clique.
The other two degrees sum to at most ten, so each degree is at least
n-11, which is positive. Every component therefore contains an edge.
The endpoint neighborhoods of that edge in its color are disjoint by
triangle-freeness, and both lie in the component. The component contains
at least 2(n-11) vertices. Two components would require
4(n-11)>n vertices, which is impossible.

**Homogeneity.** All vertices of a critical neighborhood N_i(v) have the
same set of critical colors. Reciprocity makes i critical at each vertex
there. For another color j, its internal color-j graph is connected by
the preceding argument. Reciprocity says that criticality of j agrees
across each of its edges, hence throughout the neighborhood.

### 6.2 The same two named critical colors everywhere

Write P(v) for the critical pair at v. Fix r with P(r)={i,k}, and put
X=N_i(r). Homogeneity makes P(x) constant on X, and reciprocity makes
that pair contain i. If it differs from P(r), it is {i,j} for a color j
noncritical at r. Let l be the fourth color.

Choose x in X. Its internal color-j degree is at least four, so a vertex
x' in X belongs to S=N_j(x). This is a critical neighborhood. Applying
homogeneity again, every vertex of S has pair P(x')={i,j}.

The set S avoids r because c(rx)=i. It avoids N_j(r), whose vertices
have j noncritical by reciprocity, and N_k(r), whose vertices have k
critical. Therefore

```math
S\subseteq N_i(r)\cup N_l(r).
```

Each intersection avoids color j and its different root color internally,
so each has at most five vertices. This gives |S| at most 10, contrary
to |S| at least 15. Thus critical neighbors have the same critical pair.

Every vertex has at least 31 critical neighbors. Any two such sets
intersect because 31+31>60. Their common critical neighbor shows that
all pairs agree. After one global color permutation,

```math
(d_0(v),d_1(v),d_2(v),d_3(v))=(16,16,14,14)-e_{f(v)},
\qquad f(v)\in\{0,1,2,3\}.
```

Here e_i is a coordinate unit vector. Both C profiles remain possible.
The structural argument uses degree bounds, connectivity and reciprocity;
it does not require the classification of U and T.

## 7. Compatibility and marked balance

Assume only the common degree vectors just obtained. At a root r put
X=N0(r), Y=N1(r), P=N2(r), Q=N3(r). Order the high and low colors so
these sizes are (16,16,13,14) at C1 and (15,16,14,14) at C2. Normalize
X,Y to literal critical templates with palettes (1,2,3) and (0,2,3).
At order 15 the template has its position 15 deleted.

### 7.1 The guard

For x in X, its color-0 neighbors are r and 14 or 15 vertices outside X.
In each of Y,P,Q, this support avoids color 0 and the group's root color
internally, so its size is at most five. The three sizes are therefore
four or five. The actual critical-neighborhood classification makes each
four-support a pair of complementary paths and each five-support a pair
of complementary pentagons. Exchange colors 0 and 1 for y in Y.

In particular, N0(x) intersect Y and N1(y) intersect X are the **guards**.
Their membership is exact. This does not prescribe the number of
color-1 entries in a row or color-0 entries in a column.

### 7.2 Actual visible neighborhoods

For x in X and y in Y define

```math
\Omega_x=(X\cup Y)\cap N_1(x),\qquad
\Omega_y=(X\cup Y)\cap N_0(y).
```

The full opposite neighborhoods have 15 or 16 actual vertices, so their
visible induced subgraphs embed with all colors preserved into U or T.
The palettes are (0,2,3) for Omega_x and (1,2,3) for Omega_y.
The fixed parts A_x=X intersect N1(x) and B_y=Y intersect N0(y) are the
**anchors**; the other visible vertices are **members**.

Impose an embedding condition only when the anchor has five vertices.
Its colors 2 and 3 form complementary pentagons. There are 32 such anchors
at a C1 root and 10+16=26 at a C2 root. All 31 guards at a C2 root are
retained, including the five centers whose anchors have size four.

Membership is determined by the physical cross edges: y is a member of
Omega_x exactly when c(xy)=1, and x is a member of Omega_y exactly when
c(xy)=0. Each retained embedding has at most eleven member positions.
The 26 embeddings at C2 share the same 15 by 16 cross-edge grid, and
member-pair colors come from the complete opposite root template.

### 7.3 A finite library for the embedding condition

A **table** is a relabeling of U or T onto positions 0 through 15, with
positions 0 through 4 carrying the reference pentagon: template color 1
on 01,12,23,34,40 and color 2 on the other pairs. These are the
**anchor positions**; the remaining eleven are the **nonanchor positions**.
An **ordered anchor** is a sequence of five vertices carrying this
reference coloring.

In each literal U/T matrix designate template color 0. Enumerate all
five-subsets independent in that color, and every order of each subset
matching a fixed color-1 pentagon and its color-2 complement. There
are sixteen subsets per template and ten matching orders per subset:

```math
2\cdot16\cdot10=320
```

ordered anchors in total. The finite data provide six representative
16-position colored tables, one from U and five from T. For each of
the 320 ordered anchors, an explicit bijection of all 16 positions
preserves all 120 edge colors and carries its anchor to the fixed
first five positions of one representative. Exhaustiveness is checked
over all subsets and orders, not inferred from checking six examples.
Fix an order of each physical anchor along its color-2 pentagon, which
corresponds to template color 1 in either local palette. All ten such
orders are covered.

Consequently a graph with the fixed ordered anchor embeds in U or T
if and only if its other vertices can be assigned distinct positions
among the remaining eleven in one table, with all anchor-member and
member-pair colors preserved. The forward implication composes an
actual embedding with its checked 320-entry witness. The reverse
implication composes a table assignment with the inverse witness.
These are ordinary finite matrix checks; the eleven labels have no
additional geometric meaning in the argument.

Apply this to each Omega_x and Omega_y with a five-vertex anchor. A local
witness chooses one table and distinct nonanchor positions for its members. Nonmembers
in the opposite cell have no position. Every required color is compared
with the shared physical coloring. The exact support and ordered-anchor
data are [BalancedEncodingData.lean](formal/src/UniformK61/BalancedEncodingData.lean),
with complete coverage in
[BalancedAnchorCoverage.lean](formal/src/UniformK61/BalancedAnchorCoverage.lean)
and
[BalancedAnchorSupportFinite.lean](formal/src/UniformK61/BalancedAnchorSupportFinite.lean).

### 7.4 The full-host constraints and their soundness

At a C1 root there are three template pairs UU, UT, TT: exchanging X,Y
and colors 0,1 identifies TU with UT. At C2 the unequal sizes give four
ordered pairs U-minus/U, U-minus/T, T-minus/U and T-minus/T.

For each pair, the compatibility formula uses the full K60 base, 59 root
units and 240 or 225 template-edge units. Cardinality clauses impose

```math
d_0(v),d_1(v)\leq16,\qquad d_2(v),d_3(v)\leq14
```

at every vertex. Together with the degree sum 59, these are equivalent to
the common degree vectors of Section 6. Both C profiles remain allowed.

For every center, guard selectors choose one colored path or pentagon in
the opposite template and fix its exact physical membership. For a
five-vertex anchor, six table selectors choose one table. Position variables
assign each member one of eleven nonanchor positions and assign nonmembers
none. Distinct members receive distinct positions; all anchor-member and
member-pair colors agree with the selected table and its fixed palette.

**Host-to-formula proof.** Normalize the two complete critical root groups
in the actual host and give the physical variables their actual colors.
Goodness, the root and template units, and the degree caps hold. Choose the
actual guard at each center. Classification of the actual opposite
neighborhood and the six-table library supply each retained embedding.
The auxiliary variable blocks are disjoint and their physical variables
are shared. The degree counters, guards and embeddings therefore admit
one simultaneous satisfying assignment. The reproduction encoding's
implied cross-edge clauses hold as well.

### 7.5 A C2 root and its marked brace

For each of the three C1 template pairs, form an **all-five formula** by
removing the degree clauses and forbidding every four-vertex guard choice.
The three resulting formulas are unsatisfiable.

If every vertex were C1, both common critical degrees would be 16
everywhere. The three supports of a critical neighborhood containing the
root would have total size 15, with each at most five. Every cross guard
would have size five. The witnesses of Section 7.4 would satisfy one of
the all-five formulas, a contradiction. Hence a C2 root exists.

Choose that root and any mark p in its 15-vertex critical group. Its
critical neighborhood has size 15 or 16. Name the marked color 3 and
the other high color 2, giving root sizes (14,14,16,15). An exchange of
the low colors makes the second low support have size five. The remaining
shapes are

```math
(4,5,5),\qquad(5,5,4),\qquad(5,5,5).
```

Apply the common support-and-word construction with one modification:
only the real 16-vertex high group carries a foreign template. Give the
second low support fixed pentagon coordinates, without putting a template
on the rest of its 14-vertex group. The free support is a reference path
or pentagon.

The finite projected cover checks all 5,400 normalized configurations:
nine support geometries, each with 600 words. It retains 60
support-and-word rows. Each witness supplies color-preserving maps of
the two low supports and an automorphism of the whole real 16-vertex
template, preserving every internal and cross-word edge.

Extend the low-support maps over their actual group complements. Together
with the real-template map they form one physical host permutation and
preserve both positive and negative brace membership. The marked group
contains no support. Its independent normalization has three mark choices
in U-minus and nine in T-minus, giving

```math
60(3+9)=720
```

cases: 624 with a 15-vertex brace and 96 with a 16-vertex brace. Each fixes
the root edges, both actual critical root templates, support colorings,
cross word and exact brace membership. After the common global palette
normalization, add these facts to its C2 compatibility prefix. Section 7.4
supplies all auxiliary witnesses for this same normalized coloring.
Unsatisfiability of all 720 formulas gives a contradiction.

Thus the three all-five exclusions and the 720 marked-balance exclusions
rule out every good host with the common degree vectors, and hence every
perfectly balanced host.

## 8. Completing the proof

The full case boundary is:

| Family | Formulas |
|---|---:|
| A | 360 |
| B | 5,096 |
| D/UUU | 679 |
| D/UUT | 679 |
| D/UTU | 6,576 |
| D/UTT | 6,576 |
| D/TTU | 18,204 |
| D/TTT | 18,204 |
| E/UUU | 2,037 |
| E/UUT | 6,111 |
| E/UTT | 59,184 |
| E/TTT | 163,836 |
| C1 entrances | 692 |
| C2 entrances | 7,840 |
| All-five guards | 3 |
| Mixed marked balance | 720 |
| **Total** | **296,797** |

Assume every formula in this boundary is unsatisfiable and suppose a good
four-coloring of K60 exists. The 287,542 marked exclusions give the four
strict ticket bounds. If there is an entrance, its 8,532-case cover gives
a satisfying assignment to an excluded formula. Otherwise, double counting
gives perfect balance. Section 6 gives a common critical pair, and Section 7
gives a satisfying assignment to an excluded all-five or marked-balance
formula. Both alternatives are impossible, proving the theorem.

## 9. Formal theorem and computational boundary

### The mathematical interfaces

The final theorem is
[UniformK60.ramsey60_of_exact_unsat](formal/src/UniformK60/FiniteBoundary.lean).
Its case type in [ExactInputs.lean](formal/src/UniformK60/ExactInputs.lean)
is the disjoint union of the A/B/D cases, E cases, C1/C2 entrance cases,
720 mixed marked-balance cases and three all-five owners.

The sole external premise is `ExactInputs.AllUnsat`, asserting
unsatisfiability of the explicit formula for every case. The endpoint is

```math
\left(\forall k,\ \neg\exists w\;w\models\Phi_k\right)
\ \Longrightarrow\
\left(\forall c\text{ on }K_{60},\ c\text{ is not good}\right).
```

Classification, coverage, whole-host relabeling, physical-edge identification
and simultaneous auxiliary-variable soundness are proved inside Lean.
The main interfaces are:

| Argument | Lean source and endpoint |
|---|---|
| Ticket reduction and reciprocity | [Selector.lean](formal/src/UniformK60/Selector.lean), `no_C_witness_forces_synchronized` |
| Shared physical base and signed-unit soundness | [Core.lean](formal/src/UniformK60/Core.lean), `coloring_satisfies_formula` |
| Four strict ticket bounds | [MarkedBounds.lean](formal/src/UniformK60/MarkedBounds.lean), `strict_ticket_bounds` |
| Marked host coverage | [CommonCover.lean](formal/src/UniformK60/CommonCover.lean), [CommonCompleteD.lean](formal/src/UniformK60/CommonCompleteD.lean), [CommonCompleteE.lean](formal/src/UniformK60/CommonCompleteE.lean) |
| Ordinary C1/C2 entrance cover | [CEntranceComplete.lean](formal/src/UniformK60/CEntranceComplete.lean), `ordinary_entrance_cover`, `no_entrance_of_all_unsat` |
| Common critical pair | [BalancedStructure.lean](formal/src/UniformK60/BalancedStructure.lean), `synchronized_common_pair` |
| Actual mixed host to one of 720 cases | [BalancedHostBraceCover.lean](formal/src/UniformK60/BalancedHostBraceCover.lean), `actual_C2_case` |
| Shared compatibility witnesses | [BalancedEncodingSoundness.lean](formal/src/UniformK60/BalancedEncodingSoundness.lean), `normalized_units_satisfiable` |
| Complete balanced contradiction | [BalancedEncodingBalance.lean](formal/src/UniformK60/BalancedEncodingBalance.lean), `common_pair_contradiction` |
| Complete composition | [FiniteBoundary.lean](formal/src/UniformK60/FiniteBoundary.lean), `ramsey60_of_exact_unsat` |

[Verification.lean](formal/src/UniformK60/Verification.lean) checks the
endpoint types, including an explicit formulation for ordinary symmetric
four-colorings of K60, and prints their axiom dependencies. The allowed
logical axioms are `propext`, `Classical.choice` and `Quot.sound`. The
smaller classification proofs replay 55 CNF/LRAT pairs through the checked
importer. Those traces are distinct from the large external K60 exclusions.

### Exact inputs and native results

The generators use the same common physical base for every case, together
with the marked units or balanced constraints specified above. The binding
tools checked the complete ordered content, case identities, dimensions and
hashes of the formulas defined by the fresh Lean build against the native
input catalog. The checks covered all 296,797 cases, including every
marked position and all degree, guard and embedding clauses.

We ran Kissat 4.0.4 on all 296,797 exact formulas, and every case returned
UNSAT. An independent rerun with CaDiCaL 3.0.1 is in progress. Acceptance
checks the complete case census, exact input identities, frozen solver binary,
commands, native exit codes and full output logs. The [native evidence checker](reproduce/native_evidence.py) verifies
the complete boundary against the raw records; the
[formal evidence checker](reproduce/formal_evidence.py) verifies the
mathematical build and exact-input bindings.

The proof standard is therefore a Lean-checked mathematical reduction
with explicit external native UNSAT results. The native refutations
are not kernel-checked by Lean. Their trust boundary includes the
native solver and its execution environment. Reproduction rebuilds the
mathematical development and finite tables, checks the exact input binding,
and reruns Kissat. A native verdict alone does not establish coverage of a
graph family; the host-to-formula theorems above supply that part of the proof.

Build instructions are in [formal/BUILD.md](formal/BUILD.md), and the
complete workflow is in the [reproduction guide](REPRODUCIBILITY.md).
Historical attribution of the critical classifications is recorded in
[CLASSIFICATION_PROVENANCE.md](publication/CLASSIFICATION_PROVENANCE.md).
