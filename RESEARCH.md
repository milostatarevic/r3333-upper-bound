# The research behind the proof

We prove that 61 vertices force a monochromatic triangle when every pair is
assigned one of four colors: $R(3,3,3,3)\leq61$. The proof combines structural
mathematics, exhaustive finite checks and SAT refutations. Reaching this
argument required sustained work on mathematical reductions, counterexamples,
search representations and reproducible computational evidence.

This page tells that story, including the unsuccessful directions that led to
the final approach. The complete argument is in [proof.md](proof.md), and
[REPRODUCIBILITY.md](publication/REPRODUCIBILITY.md) explains how to inspect
and rerun the computations. The complete mathematical and computational
argument is supported by the reproducible native searches and finite checks.

The research was heavily assisted by AI. GPT 5.6 in Codex's ultra mode and
Fable 5 in Claude Code's ultracode mode produced the initial A/B/D closures.
GPT-6 Pro sessions contributed successive mathematical proposals and analyses.
GPT-6 Astra in Codex's ultra mode developed the final C-profile solution.
The human author has not independently verified the complete proof; [the attribution statement](publication/ATTRIBUTION.md) explains the
roles and responsibility.

## The problem and the earlier bound

Imagine 61 points, with a line between every pair, and paint every line one
of four colors. A monochromatic triangle is a set of three points whose
three connecting lines have the same color. To prove the upper bound, we
must rule out **every** possible coloring that avoids such a triangle. We
call a hypothetical coloring that avoids them *good*.

The earlier bound of 62, due to Fettes, Kramer and Radziszowski, provided
historical context for the neighborhood approach. Our computational exclusions
are produced by the searches and finite checks supplied with this project.
The starting idea is to study a vertex through its color neighborhoods.
Choose a vertex, called the *root*. Its neighbors split into four groups
according to the color of their edge to the root. Inside any one group,
that joining color is forbidden: using it again would immediately make a
monochromatic triangle with the root.

Thus a large root neighborhood is a smaller three-color Ramsey problem.
The neighborhoods of size 15 and 16 have a particularly restrictive
classification, whose two reference types the project calls **U** and **T**.
Those letters describe local colorings after justified changes of vertex
coordinates and color names; they are not additional colors. The repository
supplies a locally proved classification and its original Lean check records;
previously published computations are not imported as assumptions.
[Classification provenance](publication/CLASSIFICATION_PROVENANCE.md) records
the retained proof sources and finite certificates.

Dropping from 62 vertices to 61 changes this structure. At order 62, the
degree bound of 16 forces at least three root neighborhoods to have size
15 or 16. At order 61 there is a new possibility: **14,14,16,16**, called
profile **C**, with only two such large neighborhoods. An argument relying
on a third classified neighborhood no longer applies automatically. The
older paper had also considered size-14 catalogues and encountered a large
extension search; their use was not an overlooked shortcut.

## The first tractable branch

Much early work concentrated on **D/UUU**. Here D describes root-neighborhood
sizes 14,15,15,16, and UUU says that the three large neighborhoods have type U.
Its closure established the first substantial part of the neighborhood
strategy and supplied a basis for extending it to the other cases.

The D/UUU timing campaign returned native UNSAT for 973 inputs in
**20.7 minutes of parallel wall time**, using about **2.35 summed solver CPU hours**. Its
minimal proof route required 679 of those inputs; the other 294 were
additional benchmarks. Parallel wall time measures the wait for the campaign;
summed CPU time measures the processor work across its workers.

A SAT solver receives Boolean constraints describing possible colorings.
**UNSAT** reports that no assignment satisfies those constraints.
**UNKNOWN**, including a run stopped at a limit, means no conclusion was
obtained. The proof presented here uses native UNSAT answers as its
computational exclusions.

The next challenge was to extend this tractable first branch into an
affordable, exhaustive route across the whole problem.

## Extending the search to A, B and the other D types

Every vertex of a hypothetical good K61 has one of five possible sorted
degree profiles, labeled A through E. The project developed exhaustive
search reductions for the relevant A, B and D root conditions. A selected
high neighbor supplies another tightly structured neighborhood; the search
then retains the compatible ways those neighborhoods can overlap.

This required more than replacing U by T in a filename. Changing a local
type can change its possible supports and symmetries. A valid reduction
must preserve the same physical vertices and edge colors, retain every
necessary overlap case, and justify any exchange of blocks. The resulting
campaigns used different finite covers where that was helpful.

Those searches completed. The original route has 360 A inputs, 5,096 B
inputs, and six D families ranging from 679 to 18,204 inputs each. A was
cheap; B and some mixed D families cost tens of CPU hours. Their success
made it reasonable to continue, but it did not measure C's difficulty.

The exact conclusion is an exclusion of specified **root conditions**,
expressed using how many neighbors are high at the opposite end of their
joining edge. Applying these exclusions at every vertex gives inequalities
that become the input to the final global argument. This retains possible
A, B and D vertices while constraining their surrounding coloring.

## Why C kept resisting

C's two size-14 neighborhoods left substantial freedom outside the two
classified size-16 neighborhoods. Several representations captured useful
pieces of this freedom without making the whole problem easy for a solver.

The attempts included stronger degree and support constraints, different
choices of marked vertices, explicit physical overlap matrices, catalogues
of size-14 colorings, and attachment descriptions that removed many local
possibilities. Some complete formulations still left thousands or more
than a million candidate labels. A smaller formula or shorter case list
did not reliably produce a faster refutation.

One defined, deduplicated historical ledger contains **169 C-related solver
executions using 102.47 CPU hours**. It records one dense conditional family
refutation, 155 capped runs and 13 interruptions. This is a specified subset
of the research, not its total cost. Some individual C attempts ran for
many CPU hours without an answer.

Conditional UNSAT results and checked small exclusions gave useful local
information, but they left a gap in the coverage of C. At that stage the search
cost could not be priced reliably. The frequently discussed “100+ CPU years”
was a scenario obtained by assuming a per-case cost across a huge catalogue,
not a measured ETA or a complexity lower bound. The long UNKNOWN runs made
finding a stronger global reduction the central research objective.

## Counterexamples changed what counted as progress

The mathematical proposals were also tested against small counterexamples.
A four-anchor counting shortcut was disproved. Other constructions showed
that individually acceptable neighborhoods need not fit together in one
coloring. A fractional model satisfied certain averaged degree and triangle
constraints without supplying an actual edge coloring. Counting many
excluded local supports did not imply that a host had to pay a separate
cost for avoiding each one.

These examples were not counterexamples to the desired Ramsey bound. They
were counterexamples to proposed steps in a proof. They helped distinguish
a useful exact local statement from an unjustified claim about all 61
vertices.

This distinction mattered repeatedly. A search can rule out a local pattern
and still leave the problem of proving that every hypothetical host contains
that pattern. A correct encoding can remain UNKNOWN. A successful small
certificate does not eliminate its parent case unless the remaining
possibilities are also covered. At one point the retained assessment
recommended parking the architecture until a new global idea appeared.

## A small local relation became useful through shared edges

The later local analysis centered on the Clebsch graph, the fixed structure
of an individual color inside a critical size-16 neighborhood. Once that
color is fixed, there are **72 compatible labeled completions** in the other
two colors. If a five-vertex anchor has no edges of the fixed color, its
remaining colors form a five-cycle and its complement; fixing that colored
anchor leaves six completions in this relation.

The useful information was not merely the number 72. Two actual
neighborhoods can refer to the **same physical edge**. If their complete
local possibilities force different colors on that edge, they cannot both
belong to the same host. This gives finite contradictions that do not need
a large general-purpose SAT search.

The project used this relation to eliminate a guarded branch called **G**.
Its assumptions specify particular five-vertex intersections and high
opposite degrees. Mathematical reductions covered that branch by 3,600
isomorphic-map labels and 10,368 remaining labels. Every label was rejected
by a checked empty local relation or an incompatible shared-edge prediction.
The portable release can now replay these finite checks in seconds.

G was substantial progress, but its guards still mattered. Excluding G did
not exclude a host in which one of those intersections or degree conditions
failed. The outstanding question remained: how could the local success be
made relevant to **every** hypothetical good coloring?

## The global connection and the final 456 cases

The final connection used a simple counting identity in a more global way.
Call an endpoint *high* on an edge when its degree in that edge's color is
at least 15. At a vertex, count highness once at the vertex's own end of
each incident edge and once at its neighbors' ends. Summing over the graph
gives equal totals: the same directed incidences have been counted in two
orders.

The A/B/D exclusions constrain these counts. The new argument shows that
either a suitable C root has an actual high endpoint in one of its small
neighborhoods, or the equality forces a very rigid alternative. In that
alternative only C/E profiles remain and the two endpoints of each edge
agree about highness. Further graph and degree counting reduces this
alternative to an impossible parity case or the already excluded G branch.

Crucially, those rigid restrictions are conclusions of a temporary
contradiction argument. They were not silently added to the subsequent
SAT inputs. The result is a justified way to find a C root with the extra
high neighbor that the next reduction needs, in the same original coloring.

That neighbor supplies a third actual neighborhood of size 15 or 16.
The overlapping three-neighborhood description has a conservative cover
of **456 cases**. Their encodings retain **all 61 vertices and all 1,830
edges**, including the previously troublesome exterior. There is no later
task of gluing separately solved pieces into a global coloring: the
remaining coloring problem is already inside each formula.

An earlier, more restricted campaign had also used 456 labels. Its answers
could not be reused after removing its two extra guards. The broader inputs
were therefore searched afresh. All 456 received matching native UNSAT
answers from Kissat and CaDiCaL. The first pass used **1.54 solver CPU hours**;
the complete broader first/replay/tail history used **4.68 solver CPU hours**,
including the original capped attempts. The second figure includes the
first; neither includes all preparation, earlier research or formalization.

This completed the proof: A/B/D supply the required inequalities; the global
argument connects G to the remaining C entrance; and every resulting full-host
C formula has a recorded refutation answer. The decisive advance was proving
that the local structure covered every remaining hypothetical coloring.

## Measured search and verification costs

The table below reports the completed searches used in the proof. These are
successful search time summed over solver processes, excluding input generation,
earlier research experiments and independent reruns. Parallel execution reduces
wall time; it does not reduce these sums.

| Search family | SAT inputs | Successful solver hours |
| --- | ---: | ---: |
| A | 360 | 0.8378 |
| B | 5,096 | 21.3611 |
| D/UUU | 679 | 1.96 |
| D/UUT | 679 | 1.7294 |
| D/UTU | 6,576 | 18.9045 |
| D/UTT | 6,576 | 18.9200 |
| D/TTU | 18,204 | 61.8776 |
| D/TTT | 18,204 | 62.0167 |
| C | 456 | 1.5417 |

The final C result was then checked with the second native solver. The cost
record preserves its unsuccessful capped attempts as well as their successful
continuations:

| C phase | Solver CPU hours |
| --- | ---: |
| Kissat | 1.5417 |
| Independent solver replay, including its capped attempts | 1.2624 |
| First continuation of the 13 unresolved replay cases | 1.1326 |
| Second continuation of the 4 remaining replay cases | 0.7402 |
| **All four phases** | **4.6769** |

Separately, a fresh replay of the 13,968 finite G checks took **2.178 CPU
seconds**. This is the cost of checking their local compatibility witnesses,
not the research that found the reduction. Exact phase definitions and source
records are linked from the [measured-cost report](publication/MEASURED_COSTS.md)
and [reproduction guide](publication/REPRODUCIBILITY.md).

## What made the final approach work

The useful lesson is to track the whole implication from a hypothetical
counterexample to a searched input. Mathematical reductions determine
whether a manageable experiment says anything about the theorem. They
also determine whether an apparent optimization has accidentally discarded
a difficult possibility.

The cost records support comparisons within their stated scopes. They do
not support a grand total assembled from overlapping campaign reports,
successful attempts, retries, solver CPU, wall time and formal checking.
In particular, the cheap D/UUU baseline never priced the other branches;
the early C failures never proved an inherent lower bound on search cost.
The successful later C representation changed what was being asked of the
solver.

The release makes that implication inspectable: it supplies the mathematical
argument, retained counterexamples, exact input hashes, solver logs,
independently written finite checkers and portable reproduction commands.
The precise verification scope, including the complete Lean reduction, is
described in [TRUST_AND_CERTIFICATION.md](publication/TRUST_AND_CERTIFICATION.md).

## Sources for the narrative

The [measured-cost report](publication/MEASURED_COSTS.md) and
[full mathematical exposition](proof.md) give the current
accepted baseline. The [reproduction guide](publication/REPRODUCIBILITY.md)
explains how to extract the evidence archive. In that extracted snapshot,
the main historical sources are:

- `support/workspace/research_handoffs/C61_FRESH_RESTART_20260918/03_SEARCH_HISTORY_AND_COSTS.md`
  and its sibling `04_FAILED_BRIDGES_AND_COUNTEREXAMPLES.md`;
- `support/workspace/research_handoffs/C61_FRESH_RESTART_20260918/evidence/history/20260916_EARLY_ROUTES_AND_OBSTRUCTIONS.md`,
  including the account of the 2004 Fettes–Kramer–Radziszowski method;
- `evidence/D/UUU/REPORT.md`, the original parallel timing baseline;
- `mathematics/retained/GLOBAL_BRIDGE_ASSESSMENT.md`, the documented limits
  of the pre-final architecture;
- `evidence/c_campaign/BROAD_456_WHOLE_C_BRIDGE_001.md`, the new global
  entrance argument, and `evidence/final_validation/FINAL_REPORT_002.md`,
  the later accepted composition.

These historical documents retain their original dates and statuses. A
document saying that C was still open describes that research checkpoint;
it does not override the later final result, and the final result does not
retroactively turn earlier UNKNOWN runs into successes.
