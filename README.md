# An improved upper bound for the Ramsey number R(3,3,3,3)

> [!NOTE]
> **Update (October 2026):** The paper accompanying this repository is now on
> arXiv:\
> [*An upper bound of 61 for the Ramsey number R(3,3,3,3)*](https://arxiv.org/abs/2610.36648)

## Changelog

### 2026-10-15

- Simplified the mathematical reduction and used one full-graph encoding throughout the proof.
- Recomputed the complete 56,723-case boundary with both SAT solvers under the same default-option, uncapped policy.
- Formalized the simplified reduction in Lean and checked its exact correspondence with every solver input.

## Result

We give a computer-assisted proof of

```math
R(3,3,3,3)\leq61.
```

Every four-coloring of the edges of the complete graph on 61 vertices
contains a monochromatic triangle. This improves the upper bound 62 proved
by Fettes, Kramer and Radziszowski in 2004.

The proof combines a mathematical reduction formalized in Lean with
**56,723 explicit SAT formulas**, each refuted by **both Kissat and CaDiCaL**.
The mathematical argument, exact input reconstruction, native execution
records and verification tools are supplied for independent review.

Start with [proof.md](proof.md) for the argument,
[measured costs](publication/MEASURED_COSTS.md) for the computation, or the
[reproduction guide](publication/REPRODUCIBILITY.md) to check the evidence.

## The idea

Choose a vertex and group its neighbors by the color of their edge to it.
Each group is a three-colored complete graph with no monochromatic triangle:
the color connecting it to the chosen vertex cannot occur inside the group.
Such a group has at most 16 vertices, and the groups of sizes 15 and 16 have
small classified families. The repository supplies its own
[Lean classification proofs](publication/CLASSIFICATION_PROVENANCE.md),
including their finite certificates.

The 60 neighbors must therefore have one of five sorted size patterns:

| Profile | Neighborhood sizes |
| --- | --- |
| A | 12, 16, 16, 16 |
| B | 13, 15, 16, 16 |
| C | 14, 14, 16, 16 |
| D | 14, 15, 15, 16 |
| E | 15, 15, 15, 15 |

A vertex sends a *ticket* across an edge if its degree in that edge's color
is at least 15. Local searches for A, B and D bound the number of tickets
received. Double counting tickets, once at the sender and once at the
receiver, leaves two possibilities: a C entrance or perfect balance.
An entrance consists of a C root and a ticket sender in one of its
14-vertex neighborhoods, and has a 346-case cover. In perfect balance,
there is no entrance and every vertex receives as many tickets as it sends.
Elementary degree and connectivity arguments then force every vertex to
have profile C with the same two colors of degree 16, giving three balanced cases.

Every case retains one coloring of all 61 vertices. Neighborhoods and their
overlaps are descriptions of that coloring, so shared edges cannot be
assigned independently. [RESEARCH.md](RESEARCH.md) explains why these choices
make the finite search possible.

## The computations

All formulas use the same **7,320 physical edge-color variables** and
**156,770 shared clauses**. These clauses assign exactly one of four colors
to each of the 1,830 edges and forbid every monochromatic triangle.

The marked cases add only signed edge facts describing the root,
classified neighborhoods, selected supports and exact neighborhood membership.
Their finite cover checks that every normalized support-and-word
configuration reaches a retained case by a symmetry of the complete host.
The three balanced cases encode template embeddings of the visible parts
of 32 opposite-color neighborhoods. Each balanced formula has 13,656
variables and 524,462 clauses, including auxiliary variables.

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
| C, marked entrance | 346 |
| C, perfect balance | 3 |
| **Total** | **56,723** |

U and T are the two critical neighborhood templates, defined in
[proof.md](proof.md). The A/B/D exclusions establish local inequalities;
they do not separately assert that those vertex profiles are absent.
Profile E is eliminated by the structural argument.

Both solvers use default search options, with no CPU or elapsed-time limit.
The required native executions used **676.77 CPU-hours** in total.
The [cost table](publication/MEASURED_COSTS.md) gives each family's CPU time,
elapsed durations, concurrency and measurement scope. CPU time is summed
over solver processes; elapsed time also reflects parallelism and other
work on the machine. Lean compilation and input verification are measured
separately.

## Verification method

This is a computer-assisted proof with a complete mathematical reduction in
Lean and external native SAT results. The theorem
[`UniformK61.WholeProof.ramsey61`](formal/src/UniformK61/WholeProof.lean)
has one computational premise, `AllNativeUnsat`, asserting that its 56,723
concrete formulas are unsatisfiable. Lean proves the exhaustive case cover,
the full-graph coordinate changes, the structural arguments and the
encoding lemmas that turn a hypothetical counterexample into a satisfying
assignment of one of those formulas.

The [input-binding tools](formal/reproduce/uniform/README.md) emit the
Lean-defined formulas and compare their complete DIMACS identities with
the native inputs. The [evidence verifier](reproduce/uniform_release.py)
checks every required result against the exact input hash, solver binary,
default-option command, raw log and exit status. All **113,446 required
solver executions** are included. The large UNSAT results remain external
computational evidence; they are not replayed in the Lean kernel.

The [portable Lean build](formal/BUILD.md) checks the entire selected
source closure without prior project artifacts, including 32 classification
modules and their 55 small CNF/LRAT pairs. The exact theorem type and axiom
dependencies are checked separately from native-result verification.
[Trust boundary](publication/TRUST_AND_CERTIFICATION.md) ·
[Formal theorem map](publication/FORMALIZATION_STATUS.md) ·
[Release checks](publication/RELEASE_CHECKS.md)

[CI](.github/workflows/verify.yml) checks manifested sources and embedded
data and builds the five-module physical-encoding target. The full
mathematical build and native searches are separate reproducible operations.

## Reproduction

Fetch the Git LFS archives, then reconstruct the complete input catalog:

```sh
git lfs install --local
git lfs pull --include='archives/*.tar.gz'
python3 -B reproduce/uniform_k61.py prepare --output /path/to/new-inputs
```

The shared base is stored once, together with a compressed catalog of
marked-case units and three balanced formulas. The
[reproduction guide](publication/REPRODUCIBILITY.md) gives commands to
authenticate the evidence, verify all recorded results, materialize an
individual formula, rerun both solvers, build the Lean proof and compare
every input with its formal definition. Python tools use the standard
library.

## AI assistance and responsibility

This research was heavily assisted by AI. GPT 5.6 in Codex with ultra
reasoning and Fable 5 in Claude Code with ultracode developed the A/B/D
reductions. GPT-6 Astra in Codex with ultra reasoning developed the C-profile
solution and mathematical formalization. GPT-6 Pro contributed mathematical
proposals and analyses.

The work has not yet undergone independent human review. The mathematical
argument, Lean sources and computational evidence are supplied for that
review. The author takes responsibility for the result, its evidence and
corrections. [Full attribution](publication/ATTRIBUTION.md)

## Repository layout

| Path | Purpose |
| --- | --- |
| [proof.md](proof.md) | Human-readable proof and its computational premises |
| [RESEARCH.md](RESEARCH.md) | Mathematical strategy and research contribution |
| [classification/](classification/README.md) | Critical-neighborhood proofs and small certificates |
| [formal/](formal/README.md) | Lean proof, pinned source build and exact input binding |
| [reproduce/](publication/REPRODUCIBILITY.md) | Input generation, solver execution and evidence verification |
| [publication/](publication/RELEASE_CHECKS.md) | Dependency map, computational records and verification details |
| `archives/evidence-v1.tar.gz` | Authenticated finite support and word catalogs |
| `archives/evidence-v2.tar.gz` | Current inputs, native results and mathematical verification records |

We welcome expert review of the mathematical argument and its correspondence
with the computational inputs.

## References

1. S. Fettes, R. L. Kramer and S. P. Radziszowski,
   [*An Upper Bound of 62 on the Classical Ramsey Number R(3,3,3,3)*](https://combinatorialpress.com/article/ars/Volume%20072/volume-72-paper-5.pdf),
   Ars Combinatoria 72 (2004), 41–63.
2. S. P. Radziszowski, [*Small Ramsey Numbers*](https://doi.org/10.37236/21).
3. [Local classification proofs and provenance](publication/CLASSIFICATION_PROVENANCE.md).
