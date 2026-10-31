# An improved upper bound for the Ramsey number R(3,3,3,3)

**Current result: R(3,3,3,3) ≤ 60.** The mathematical reduction is formalized
in Lean, and every required SAT formula has been refuted by Kissat. Independent
verification with CaDiCaL is running.

**Version referenced by the K61 paper:** the [complete K61 proof, verified
with both Kissat and CaDiCaL](https://github.com/milostatarevic/r3333-upper-bound/tree/3d6910a2ef8a36a3fa3ad78a44f9f82e1f31f1c2)
is pinned to that commit. The [arXiv paper](https://arxiv.org/abs/2610.36648v1)
describes that version; this repository now contains the K60 result.

## Changelog

- **2026-10-30:** Proved **R(3,3,3,3) ≤ 60** by extending the same marked-neighborhood and ticket-counting method to six profiles and mixed perfect balance. Formalized the mathematical reduction in Lean and checked its exact correspondence with every solver input; all **296,797 formulas** were refuted by Kissat. Independent CaDiCaL verification is running.
- **2026-10-27:** Released the complete **R(3,3,3,3) ≤ 61** proof, with all **56,723 formulas** refuted by both Kissat and CaDiCaL, and the [arXiv paper](https://arxiv.org/abs/2610.36648v1). The [repository version cited by the paper](https://github.com/milostatarevic/r3333-upper-bound/tree/3d6910a2ef8a36a3fa3ad78a44f9f82e1f31f1c2) is preserved at its exact commit.
- **2026-10-15:** Simplified the mathematical reduction and used one full-graph encoding throughout the proof. Recomputed the complete 56,723-case boundary with both SAT solvers under the same default-option, uncapped policy. Formalized the simplified reduction in Lean and checked its exact correspondence with every solver input.

## Result

We give a computer-assisted proof of

```math
R(3,3,3,3)\leq60.
```

Every four-coloring of the edges of the complete graph on 60 vertices
contains a monochromatic triangle. This improves the upper bound 62 proved
by Fettes, Kramer and Radziszowski in 2004.

The proof combines a mathematical reduction formalized in Lean with
**296,797 explicit SAT formulas**, each refuted by **Kissat**.
The mathematical argument, exact input reconstruction, native execution
records and verification tools are supplied for independent review.

Start with [proof.md](proof.md) for the argument,
[measured costs](publication/MEASURED_COSTS.md) for the computation, or the
[reproduction guide](REPRODUCIBILITY.md) to check the evidence.

## The idea

Choose a vertex and group its neighbors by the color of their edge to it.
Each group is a three-colored complete graph with no monochromatic triangle:
the color connecting it to the chosen vertex cannot occur inside the group.
Such a group has at most 16 vertices, and the groups of sizes 15 and 16 have
small classified families. The repository supplies its own
[Lean classification proofs](publication/CLASSIFICATION_PROVENANCE.md),
including their finite certificates.

The 59 neighbors must therefore have one of six sorted size patterns:

| Profile | Neighborhood sizes |
| --- | --- |
| A | 11, 16, 16, 16 |
| B | 12, 15, 16, 16 |
| C1 | 13, 14, 16, 16 |
| D | 13, 15, 15, 16 |
| C2 | 14, 14, 15, 16 |
| E | 14, 15, 15, 15 |

A vertex sends a *ticket* across an edge if its degree in that edge's color
is at least 15. Local searches for A, B, D and E bound the number of tickets
received. Double counting tickets, once at the sender and once at the
receiver, leaves two possibilities: a C1 or C2 entrance, or perfect balance.
An entrance consists of a C1 or C2 root and a ticket sender in one of its
noncritical neighborhoods, with covers of 692 and 7,840 cases. In perfect
balance, there is no entrance and every vertex receives as many tickets as
it sends. Elementary degree and connectivity arguments then force every
vertex to have profile C1 or C2 with the same two critical colors. Three
auxiliary exclusions give a C2 root; its marked-neighborhood construction
leaves 720 balanced cases.

Every case retains one coloring of all 60 vertices. Neighborhoods and their
overlaps are descriptions of that coloring, so shared edges cannot be
assigned independently. [RESEARCH.md](RESEARCH.md) explains why these choices
make the finite search possible.

## The computations

All formulas use the same **7,080 physical edge-color variables** and
**149,270 shared clauses**. These clauses assign exactly one of four colors
to each of the 1,770 edges and forbid every monochromatic triangle.

The marked cases add only signed edge facts describing the root,
classified neighborhoods, selected supports and exact neighborhood membership.
Their finite covers check that every normalized support-and-word
configuration reaches a retained case by a symmetry of the complete host.
The 720 mixed-balance cases encode template embeddings of the visible parts
of 26 opposite-color neighborhoods and impose the global degree caps and
four- or five-vertex guard conditions. The three C1 auxiliary formulas use
32 such embeddings and forbid four-vertex guards.

| Family | SAT formulas |
| --- | ---: |
| A | 360 |
| B | 5,096 |
| D / UUU | 679 |
| D / UUT | 679 |
| D / UTU | 6,576 |
| D / UTT | 6,576 |
| D / TTU | 18,204 |
| D / TTT | 18,204 |
| E / UUU | 2,037 |
| E / UUT | 6,111 |
| E / UTT | 59,184 |
| E / TTT | 163,836 |
| C1 entrances | 692 |
| C2 entrances | 7,840 |
| All-five guards | 3 |
| Mixed marked balance | 720 |
| **Total** | **296,797** |

U and T are the two critical neighborhood templates, defined in
[proof.md](proof.md). The A/B/D/E exclusions establish local inequalities;
they do not separately assert that those vertex profiles are absent.

Kissat uses default search options. Cases unresolved after a five-minute
first pass are retried with longer limits; all required cases finished UNSAT.
The complete attempt histories, including timeouts and interrupted attempts,
are retained in the native evidence archive. The native executions used
**886.75 CPU-hours** in total. The [cost table](publication/MEASURED_COSTS.md)
gives each family's CPU time, elapsed durations, concurrency and measurement
scope. CPU time is summed over solver processes; elapsed time also reflects
parallelism and other work on the machine.

## Verification method

This is a computer-assisted proof with a complete mathematical reduction in
Lean and external native SAT results. The theorem
[`UniformK60.ramsey60_of_exact_unsat`](formal/src/UniformK60/FiniteBoundary.lean)
has one computational premise, `ExactInputs.AllUnsat`, asserting that its
296,797 concrete formulas are unsatisfiable. Lean proves the exhaustive case
covers, the full-graph coordinate changes, the structural arguments and the
encoding lemmas that turn a hypothetical counterexample into a satisfying
assignment of one of those formulas.

The [input-binding tools](REPRODUCIBILITY.md#rebuild-and-bind-the-formal-definitions)
emit the Lean-defined formulas and compare their complete DIMACS identities
with the native inputs. The [evidence verifier](reproduce/native_evidence.py)
checks every required result against the exact input hash, solver binary,
command, raw log and exit status. All **296,797 required UNSAT outcomes** and
the complete attempt histories are included. The large UNSAT results remain
external computational evidence; they are not replayed in the Lean kernel.

The [portable Lean build](formal/BUILD.md) checks the entire selected
source closure without prior project artifacts, including the classification
modules and their 55 small CNF/LRAT pairs. The exact theorem type and axiom
dependencies are checked separately from native-result verification.

[CI](.github/workflows/verify.yml) checks manifested sources and embedded
data and builds the five-module physical-encoding target. The full
mathematical build and native searches are separate reproducible operations.
The [manual full-build workflow](.github/workflows/full-lean.yml) rebuilds the
complete theorem; the [evidence workflow](.github/workflows/evidence.yml)
checks the retained formal and native evidence.

## Reproduction

Fetch the Git LFS archives:

```sh
git lfs install --local
git lfs pull --include='archives/*.tar.gz'
```

The shared base is stored once, together with compact signed-unit catalogues
and balance prefixes. The [reproduction guide](REPRODUCIBILITY.md) gives
commands to authenticate the evidence, verify all recorded results,
materialize an individual formula, rerun a solver, build the Lean proof and
compare every input with its formal definition. Python tools use the standard
library. The [release index](publication/checks/K60_RELEASE.json) records the
archive hashes and accepted build, binding and native evidence.

## AI assistance and responsibility

This research was heavily assisted by AI. GPT 5.6 in Codex with ultra
reasoning and Fable 5 in Claude Code with ultracode developed the A/B/D
reductions. GPT-6 Astra in Codex with ultra reasoning developed the C-profile
solution and mathematical formalization. GPT-6 Pro contributed mathematical
proposals and analyses.

The mathematical argument, Lean sources and computational evidence are
intended for independent review. The author directs the research and takes
responsibility for the result, its evidence and corrections.
[Full attribution](publication/ATTRIBUTION.md).

## Repository layout

| Path | Purpose |
| --- | --- |
| [proof.md](proof.md) | Human-readable proof and its computational premise |
| [RESEARCH.md](RESEARCH.md) | Mathematical strategy and the role of the finite searches |
| [REPRODUCIBILITY.md](REPRODUCIBILITY.md) | Archive checks, fresh build and exact-input replay |
| [formal/](formal/README.md) | Complete selected Lean sources, classification data and build configuration |
| [formal/SOURCE_INDEX.json](formal/SOURCE_INDEX.json) | Source hashes and formal-capsule correspondence |
| [reproduce/](reproduce/) | Portable evidence verifiers and individual input exporter |
| [.github/workflows/verify.yml](.github/workflows/verify.yml) | Source audit and small encoding build |
| [archives/](archives/) | Formal and native K60 capsules, member indexes and archive checksums |
| [publication/checks/K60_RELEASE.json](publication/checks/K60_RELEASE.json) | Build, bindings, capsule and native evidence identities |

We welcome expert review of the mathematical argument and its correspondence
with the computational inputs.

## References

1. S. Fettes, R. L. Kramer and S. P. Radziszowski,
   [*An Upper Bound of 62 on the Classical Ramsey Number R(3,3,3,3)*](https://combinatorialpress.com/article/ars/Volume%20072/volume-72-paper-5.pdf),
   Ars Combinatoria 72 (2004), 41–63.
2. S. P. Radziszowski, [*Small Ramsey Numbers*](https://doi.org/10.37236/21).
3. [Classification proofs and provenance](publication/CLASSIFICATION_PROVENANCE.md).
