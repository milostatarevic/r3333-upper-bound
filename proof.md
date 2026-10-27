# An improved upper bound for the Ramsey number R(3,3,3,3)

## The result and the proof route

**Theorem.** Every four-coloring of the edges of the complete graph on 61
vertices contains a monochromatic triangle. Consequently,

```math
R(3,3,3,3)\leq61.
```

Call an edge coloring **good** if it contains no monochromatic triangle.
The proof assumes a good coloring of one complete graph on 61 vertices and
derives a contradiction. Combinatorial arguments reduce this hypothetical
coloring to an exhaustive family of Boolean formulas. Every formula describes
the same 61 physical vertices; overlapping neighborhoods share their actual
edge colors.

The finite boundary has **56,723 cases**: 56,374 marked A/B/D cases, 346
marked C cases, and three balance cases. The mathematical reductions,
finite coverage arguments, and implications from a host coloring to these
formulas are formalized in Lean. Unsatisfiability of the exact formulas is
the external computational premise, checked with Kissat and CaDiCaL. The
precise division between the Lean proof and native computations is given in
[Section 9](#9-formal-theorem-and-computational-boundary).

The argument has three parts. First, double counting tickets converts
local bounds for profiles A, B and D into a choice between a marked C
configuration and perfect balance. The same marked-neighborhood construction
excludes the C configuration. In perfect balance, elementary counting forces
every vertex to have the same two colors of degree 16. The classification of
the resulting actual neighborhoods then supplies three full-host
compatibility formulas, all unsatisfiable.

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
12\leq d_i(v)\leq16,\qquad \sum_{i=0}^{3}d_i(v)=60.
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

The four deficits 16-d_i(v) are nonnegative and sum to four. Their partitions
give exactly five sorted degree profiles:

| Profile | Sorted degrees | Critical neighborhoods | Tickets sent, w(v) |
|---|---|---:|---:|
| A | (12,16,16,16) | 3 | 48 |
| B | (13,15,16,16) | 3 | 47 |
| C | (14,14,16,16) | 2 | 32 |
| D | (14,15,15,16) | 3 | 46 |
| E | (15,15,15,15) | 4 | 60 |

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

The marked A/B/D case cover in Section 4 proves the strict bounds

```math
\begin{array}{c|ccc}
\text{profile}&A&B&D\\
\hline
H(v)&\leq47&\leq46&\leq45.
\end{array}
```

An **entrance** is a pair (r,p) where r has profile C, p belongs to one of
its 14-vertex neighborhoods, and p sends r a ticket. If there is no entrance,
a C vertex can receive tickets only from its two 16-vertex neighborhoods.
Thus H(v) is at most 32=w(v) at C. At E it is at most 60=w(v).

Together with the A/B/D bounds this gives H(v) at most w(v) everywhere.
The differences w(v)-H(v) are nonnegative integers with sum zero, so each
is zero. The strict-deficit profiles A, B and D cannot occur. Every C
vertex receives a ticket from all 32 neighbors in its critical colors, and
every E vertex receives one from all its neighbors.

Call a good coloring **perfectly balanced** if it has no entrance and
H(v)=w(v) everywhere. We have proved the following alternative, subject
only to the A/B/D exclusions: either an entrance exists, or the host is
perfectly balanced and has only profiles C and E. Section 5 excludes the
first possibility; Sections 6 and 7 exclude the second.

## 3. One physical encoding and a common marked construction

### 3.1 The full-host base

For every unordered edge e of K61 and every color i, use a Boolean variable
x_(e,i) asserting that e has color i. There are

```math
4\binom{61}{2}=7,320
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
7\binom{61}{2}+4\binom{61}{3}=156,770
```

base clauses. Its satisfying assignments correspond exactly to good
four-colorings of K61.

A **marked case** adds only signed physical edge facts to this base.
A positive fact fixes an edge color; a negative fact excludes that color.
It is encoded by the corresponding unit clause. Repeated facts do not
change satisfiability, and the binding checks retain the exact ordered
unit lists used to generate the inputs. All A/B/D and C marked cases have
7,320 variables. The three balance cases use this same physical base with
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

1. All 60 root edges, according to their root cells.
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
A symmetry uses one permutation sigma of all 61 vertices and one global
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
cell. These maps fix r and R3 and combine into one permutation of all 61
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

## 4. The A, B and D ticket bounds

Suppose a root violates its proposed bound. Its incoming ticket count is
at least 48, 47 or 46 in profiles A, B or D.

First order the root-cell sizes as (12,16,16,16), (13,15,16,16), or
(14,15,15,16), respectively. For A, order the types of the three
16-cells. For B, order the types of its two 16-cells. For D, order the
types of its two 15-cells. Each exchange of cells is accompanied by the
same global permutation of their root colors and fixed-palette
normalization of the templates.

Only 44 neighbors lie outside any 16-cell, so every such cell contains
at least four, three or two ticket senders, respectively. In the resulting
R3, choose one as p and place its template with p at reference position 15.
The cells R1 and R2 are critical, so the construction of Section 3 applies.

For D, the additional exchange of R1 and R2, together with colors 1 and 2,
preserves the full host conditions. A palette-realizing vertex map fixing
the mark restores the template on R3, and a free-support relabeling restores
its reference coloring. When the two foreign types agree, this identifies
shapes (5,4,5) and (5,5,4). With two foreign T types and shapes (4,5,5) or
(5,5,5), the two five-support orbits may also be ordered; when they agree,
all word orbits remain included.

The table counts retained cases. Completeness is checked by the finite
coverage condition of Section 3.3, which does not require a minimal list.
A row with marked types U,T is used once for each marked type. A
three-letter family name lists the types of R1, R2, R3 in that order.

| Profile | Foreign types | Marked types | (4,5,5) | (5,4,5) | (5,5,4) | (5,5,5) | Cases per marked type |
|---|---|---|---:|---:|---:|---:|---:|
| A | UU | U,T | 4 | 4 | 4 | 2 | 14 |
| A | UT | T | 16 | 16 | 20 | 4 | 56 |
| A | TT | T | 76 | 92 | 92 | 16 | 276 |
| B | UU | U,T | 36 | 40 | 36 | 10 | 122 |
| B | UT | T | 168 | 184 | 204 | 36 | 592 |
| B | TU | U,T | 168 | 220 | 168 | 36 | 592 |
| B | TT | T | 828 | 1,084 | 996 | 168 | 3,076 |
| D | UU | U,T | 189 | 408 | included through exchange | 82 | 679 |
| D | UT | U,T | 1,824 | 1,992 | 2,388 | 372 | 6,576 |
| D | TT | U,T | 5,256 | 11,892 | included through exchange | 1,056 | 18,204 |

For every family in the table, finite checks combined with the transport
proofs establish the coverage condition of Section 3.3 on every normalized
support pair and every one of its 600 words. Each target includes its
complete root and template facts, free-support pattern, cross word and
signed membership. Both
marked-template choices are included whenever the row lists U,T.

### Excluding the selected roots

The family totals are

```math
360\quad\text{(A)},\qquad 5,096\quad\text{(B)},\qquad
2(679+6,576+18,204)=50,918\quad\text{(D)}.
```

Every selected root supplies an actual mark, and the covers just proved
send its host to one of these 56,374 cases. The physical coloring would
satisfy the corresponding base and units. Unsatisfiability of every case
therefore proves H at most 47, 46 and 45 for A, B and D. These are ticket
bounds; they do not assert that an isolated root of one of those profiles
is impossible without the global counting argument.

## 5. Excluding C entrances

An entrance supplies a C root r and a mark p in a 14-cell. Name that cell
R3, the other 14-cell R0, and the two 16-cells R1,R2. The sizes are
(14,16,16,14), and d3(p) is 15 or 16. Place templates only on R1 and R2.
The common marked construction applies to the actual brace N3(p).

Exchange the foreign cells and their colors to order the foreign types as
UU, UT or TT. For each shape, use their whole-template support orbits and
the support-word actions from Section 3. The free cell contributes only
its chosen support and its complement, so its size 14 causes no extension
assumption. The marked cell is fixed by these actions and has no placed
template. All four support shapes are retained:

| Foreign types | (4,5,5) | (5,4,5) | (5,5,4) | (5,5,5) | Total |
|---|---:|---:|---:|---:|---:|
| UU | 4 | 4 | 4 | 2 | 14 |
| UT | 16 | 16 | 20 | 4 | 56 |
| TT | 76 | 92 | 92 | 16 | 276 |
| **Total** | **96** | **112** | **116** | **22** | **346** |

The same finite support and word action data establish the coverage
condition of Section 3.3 for these lists. Extending the free-support maps
to the whole 14-cell preserves every additional negative membership fact.

The canonical physical layout is root 0, free cell 1 through 14, first
foreign cell 15 through 30, second foreign cell 31 through 46, and marked
cell 47 through 60, with mark 60. Their root colors are 0,1,2,3. Each
case fixes all root spokes, both foreign templates, the free-support
coloring, its cross word, and exact marked-color membership on every
other vertex. The root-mark edge is supplied by the root spokes; the
remaining 59 membership facts are explicit units.

The finite case data are [c_entrances.json](reproduce/data/c_entrances.json).
The direct generator [uniform_c.py](reproduce/uniform_c.py) constructs
these facts on the canonical layout. The complete finite join and the generic normalized-entrance
[physical cover](formal/src/UniformK61/CEntranceCover.lean),
`CEntrance.physical_cover`, prove that every entrance yields a satisfying
assignment to one of these 346 exact formulas. Since all are unsatisfiable, no entrance exists.

## 6. Perfect balance forces a common degree vector

Assume perfect balance. Section 2 leaves only C and E, with every possible
incoming ticket in the indicated cells present.

### 6.1 Reciprocity and internal connectivity

**Reciprocity.** The color of an edge is critical at one endpoint if and
only if it is critical at the other. Indeed, if u sends v a ticket and v
is E, that color has degree 15 at v. If v is C, the ticket must enter
one of its 16-cells, so the color has degree 16 at v. In either case v
sends a ticket back.

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

### 6.2 Excluding E

There is a C vertex r. Otherwise all vertices would be E and every
color graph would be 15-regular on 61 vertices, giving the impossible
odd degree sum 61 times 15. Name the critical colors at r as 0 and 1
and write

```math
X=N_0(r),\quad Y=N_1(r),\quad P=N_2(r),\quad Q=N_3(r).
```

Their sizes are 16,16,14,14. Every E vertex lies in X union Y by
reciprocity. Suppose e is E. Its containing cell X or Y consists entirely
of E vertices by homogeneity. Each internal color degree in this
three-colored K16 is exactly five. Color 2 occurs inside either cell, so
N2(e) contains an E vertex there. Since e is E, d2(e)=15 and N2(e) is
critical. Homogeneity then makes all its vertices E, so it is contained
in X union Y.

Its intersection with X forbids colors 2 and 0 internally, and its
intersection with Y forbids colors 2 and 1. Both intersections are good
two-colored cliques of size at most five. This gives

```math
15=|N_2(e)|\leq5+5=10,
```

a contradiction. Every vertex is therefore C.

### 6.3 The same two named critical colors everywhere

Take any root r and name its critical pair 0,1. If x belongs to N0(r),
then 0 is critical at x by reciprocity. Suppose another critical color
at x were j in {2,3}. Since d_j(r)=14, reciprocity makes j noncritical
at every vertex of N_j(r). Thus x has no color-j neighbor in N_j(r).
The root itself is not a color-j neighbor of x. In each of the other
three root cells, the color-j neighbors of x avoid both j and the cell's
root color internally and number at most five. Therefore

```math
d_j(x)\leq15,
```

contradicting the degree 16 of a critical color at a C vertex. The pair
at x is {0,1}; the same proof applies in N1(r). Since r was arbitrary,
the endpoints of every critical edge have the same critical pair.

Each vertex has 32 critical neighbors. Any two such sets intersect,
because 32+32>61. The common critical neighbor shows that any two
vertices have the same pair. After one global color permutation,

```math
d_0(v)=d_1(v)=16,\qquad d_2(v)=d_3(v)=14
\quad\text{for every }v.
```

This entire structural argument uses elementary degree bounds,
connectivity, reciprocity and parity. It does not need the internal
classification of U and T.

## 7. Three balance formulas

Assume the common degree vector just obtained. At a root r, use X,Y,P,Q
as in Section 6. Normalize the complete colorings on X and Y to literal
templates V_X,V_Y in {U,T}, with palettes (1,2,3) and (0,2,3).

### 7.1 The guard

For x in X, its 16 color-0 neighbors are r and 15 vertices outside X.
In each of Y,P,Q, this support avoids color 0 and the root color of that
cell internally, so it has at most five vertices. All three supports
must have exactly five. Likewise, every y in Y has exactly five color-1
neighbors in each of X,P,Q.

In particular, every X row of the cross-edge grid has five color-0
entries and every Y column has five color-1 entries. This is the
**guard**. It does not assert that a row has five color-1 entries or
that a column has five color-0 entries.

### 7.2 Actual visible neighborhoods

For each x in X and y in Y define

```math
\Omega_x=(X\cup Y)\cap N_1(x),\qquad
\Omega_y=(X\cup Y)\cap N_0(y).
```

The full neighborhoods N1(x) and N0(y) have 16 actual vertices, so
classification provides injective color-preserving embeddings of their
visible induced subgraphs into U or T. The palette for Omega_x is
(0,2,3), and for Omega_y it is (1,2,3).

Inside Omega_x the five known vertices

```math
A_x=X\cap N_1(x)
```

form an **anchor**. Inside Omega_y the corresponding anchor is
B_y=Y intersect N0(y). These anchors have five vertices because the
internal template color degrees are five. Their colors 2 and 3 form
complementary pentagons.

Call the visible vertices outside the anchor **members**. They are
determined by physical edge colors: y in Y belongs to Omega_x precisely
when c(xy)=1, and x in X belongs to Omega_y precisely when c(xy)=0.
These membership colors differ from the guard colors. Each visible
neighborhood has at most eleven members. Its exact member count is not
fixed in the encoding. The 32 local embedding checks all refer to the same 256
physical edges between X and Y. A check centered at x also reads
the five anchor rows A_x; one centered at y reads the five anchor
columns B_y. Member-pair colors are the fixed internal colors of
the opposite root template.

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

Apply this to each Omega_x and Omega_y. A local witness chooses one
table and distinct nonanchor positions for its members. Nonmembers
in the opposite cell have no position. Every required color is compared
with the shared physical coloring. The exact support and ordered-anchor
data are [balance_anchors.json](reproduce/data/balance_anchors.json),
with complete coverage in
[BalancedAnchorCoverage.lean](formal/src/UniformK61/BalancedAnchorCoverage.lean)
and
[BalancedAnchorSupportFinite.lean](formal/src/UniformK61/BalancedAnchorSupportFinite.lean).

### 7.4 The full-host constraints and their soundness

For each template pair V_X,V_Y form a formula on all 61 vertices.
In addition to the common base it contains 60 root-edge units, 240
template-edge units, the guard's support choices, and all 32
visible-neighborhood embedding conditions. The common degree vector
proved in Section 6 ensures that each actual opposite neighborhood
has order 16 and therefore supplies a classified template embedding.

For each visible neighborhood, sixteen guard selectors choose exactly
one five-subset of the opposite template independent in its designated
color and fix guard membership in both directions. Six table selectors choose exactly one
table. Position variables give each member exactly one of eleven
nonanchor positions and give nonmembers none. The assignment is
injective and checks every anchor-member and member-pair color. Literal comparisons across the
six tables allow state-independent color and support clauses to be
shared. The resulting clauses retain the stated embedding condition.
The explicit cross-edge one-color clauses and mixed-triangle clauses
are consequences of the common physical base and fixed templates.

The variable allocation is disjoint:

| Meaning | Variables |
|---|---:|
| Physical edge colors | 7,320 |
| Guard subset choices | 512 |
| Local member positions and table choices | 5,824 |
| **Total** | **13,656** |

Each balance formula has **524,462 clauses**. Its generator is
[uniform_balance.py](reproduce/uniform_balance.py), and its exact
Lean definition is
[BalancedEncodingDefs.lean](formal/src/UniformK61/BalancedEncodingDefs.lean).

**Host-to-formula proof.** Normalize the root partition and its two high
cells in the actual host. Assign physical edge variables their actual
colors, satisfying goodness and the fixed edge clauses. For x in X,
select the guard subset N0(x) intersect Y. Classification of the actual
N1(x) and the anchor library supply one table and an injective placement
of Omega_x, sending its ordered anchor to positions 0 through 4.
Select that table and set position variables true exactly for its
placed members. All required colors agree with the actual host, and
member-pair colors are already fixed by V_Y. Apply the same construction
for y in Y with the colors and cells exchanged. The auxiliary ranges
are disjoint and physical colors are shared, so these witnesses satisfy
all clauses simultaneously, including the implied cross-edge clauses.

There are initially four ordered template pairs. Exchanging X and Y
and globally exchanging colors 0 and 1 takes TU to UT, preserves
the named degree vector, and carries every visible-neighborhood
condition to its counterpart. Only **UU, UT and TT** are therefore
required. This proves that every good host with the common degree
vector satisfies one of the three exact formulas. Their
unsatisfiability excludes the common degree vector and hence
perfect balance.

## 8. Completing the proof

The full case boundary is:

| Family | Cases | Physical graph |
|---|---:|---|
| A | 360 | K61 |
| B | 5,096 | K61 |
| D/UUU | 679 | K61 |
| D/UUT | 679 | K61 |
| D/UTU | 6,576 | K61 |
| D/UTT | 6,576 | K61 |
| D/TTU | 18,204 | K61 |
| D/TTT | 18,204 | K61 |
| C entrances | 346 | K61 |
| Balance UU, UT, TT | 3 | K61 |
| **Total** | **56,723** | |

Assume every formula in this boundary is unsatisfiable, and suppose a
good four-coloring of K61 exists. The 56,374 A/B/D exclusions give the
strict ticket bounds. If there is an entrance, the direct 346-case C
cover gives a satisfying assignment to a forbidden formula. If there
is no entrance, double counting tickets gives perfect balance. Sections 6
and 7 then give a satisfying assignment to one of the three forbidden
balance formulas. Both alternatives are impossible. This proves the
theorem.

## 9. Formal theorem and computational boundary

### The mathematical interfaces

The final Lean theorem is
[UniformK61.WholeProof.ramsey61](formal/src/UniformK61/WholeProof.lean).
Its case type is the disjoint union of the complete A/B/D case type,
the 346 C cases, and the three balance owners. The companion theorem
`native_case_count` proves that this type has cardinality 56,723.

The only external premise is `AllNativeUnsat`, which asserts
unsatisfiability of `WholeProof.formula k` for every case k. In
mathematical notation the endpoint has the form

```math
\left(\forall k,\ \neg\exists w\;w\models\Phi_k\right)
\ \Longrightarrow\
\left(\forall c\text{ on }K_{61},\ c\text{ is not good}\right).
```

The premise concerns the exact formulas. Classification, case coverage,
whole-host relabeling, physical-edge identification and auxiliary-variable
soundness are established inside the mathematical development. The main
interfaces are:

| Argument | Lean source and endpoint |
|---|---|
| Double counting of tickets and entrance-or-balance reduction | [Selector.lean](formal/src/Ramsey61/Selector.lean), `no_C_witness_forces_synchronized_CE` |
| Shared physical base and signed-unit soundness | [Core.lean](formal/src/UniformK61/Core.lean), `coloring_satisfies_formula` |
| A/B/D ticket bounds | [ABDProof.lean](formal/src/UniformK61/ABDProof.lean), `selector` |
| Marked-configuration coverage | [CommonCover.lean](formal/src/UniformK61/CommonCover.lean), [UUFiniteCover.lean](formal/src/UniformK61/UUFiniteCover.lean), and [UnitTransport.lean](formal/src/UniformK61/UnitTransport.lean) |
| Direct C entrance cover | [CEntranceFinal.lean](formal/src/UniformK61/CEntranceFinal.lean), `actual_C_cover` |
| Elementary common-degree reduction | [BalancedStructurePair.lean](formal/src/UniformK61/BalancedStructurePair.lean), `synchronized_uniform_complete` |
| Actual balanced host to one of three formulas | [BalancedEncodingActual.lean](formal/src/UniformK61/BalancedEncodingActual.lean), `actual_uniform_cover` |
| Complete composition and case count | [WholeProof.lean](formal/src/UniformK61/WholeProof.lean), `ramsey61`, `native_case_count` |

The exact endpoint type and its axiom reports are checked by
[Audit.lean](formal/reproduce/uniform/Audit.lean). The allowed logical
axioms are Lean's standard `propext`, `Classical.choice` and `Quot.sound`.
The smaller-order classification proofs replay their 55 supplied
CNF/LRAT pairs through the checked importer. These checked classification
traces are distinct from the external native K61 computations.

### Exact inputs and native results

The executable generator
[uniform_k61.py](reproduce/uniform_k61.py) uses the same common
physical base for every case, together with the marked units or
balanced constraints specified above. The
[uniform binding tools](formal/reproduce/uniform/README.md) emit
the formulas from the fresh Lean build and compare their complete
ordered content, case identities, dimensions and hashes with the
native input catalog. The joint check covers all 56,723 cases and every
marked-template choice in their definitions.

Each exact formula is run with Kissat 4.0.4 and CaDiCaL 3.0.1 using
default options and no CPU or elapsed-time cutoff. The resulting
113,446 required native outcomes are UNSAT. Acceptance checks the
complete case census, exact input identities, frozen solver binaries,
commands, native exit codes and full output logs. The release checker
[uniform_release.py](reproduce/uniform_release.py) verifies the
complete current boundary against the raw records and the mathematical
build and binding receipts.

The proof standard is therefore a Lean-checked mathematical reduction
with explicit external native UNSAT results. The native refutations
are not kernel-checked by Lean. Their trust boundary includes the
native solvers and their execution environment; using two solvers
provides an independent computational cross-check. Reproduction rebuilds
the mathematical development and finite tables, checks the exact
input binding, and reruns the specified solvers. A native verdict
alone does not establish coverage of a graph family; the host-to-formula
theorems above supply that part of the proof.

Build instructions are in [formal/BUILD.md](formal/BUILD.md), and the
complete workflow is in the
[reproduction guide](publication/REPRODUCIBILITY.md). Historical
attribution of the critical classifications is recorded in
[CLASSIFICATION_PROVENANCE.md](publication/CLASSIFICATION_PROVENANCE.md).
