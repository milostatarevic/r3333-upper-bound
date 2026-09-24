# An improved upper bound for the Ramsey number R(3,3,3,3)

## Result

We give a computer-assisted proof of

```math
R(3,3,3,3)\leq61.
```

Every four-coloring of the edges of the complete graph on 61 vertices
contains a monochromatic triangle. This improves the upper bound 62 proved
by Fettes, Kramer and Radziszowski in 2004.

The proof combines structural mathematics, exhaustive finite enumeration
and SAT solving. Its complete case cover uses **56,830 SAT formulas**, all
refuted by **both Kissat and CaDiCaL**, and **13,968 finite compatibility checks**.
We provide the mathematical argument, exact input reconstruction, solver
results and checking tools so readers can inspect the proof and rerun the
computations.

Start with [proof.md](proof.md) for the complete argument,
[search costs](#search-costs) for the computation, and
[verification](#verification-method) for the verification scope.

## Motivation

The four-color triangle Ramsey number is a small-looking problem with a large
search space. The April 2026 revision of *Small Ramsey Numbers* records

```math
51\leq R(3,3,3,3)\leq62.
```

The upper bound 62 was already computer-assisted. Moving from 62 to 61 requires
excluding a smaller hypothetical coloring, so a case that disappears in the
older argument may survive at the new order. The central question was whether
enough structure could be extracted before search to make an exhaustive
computation practical. [Earlier bound](https://combinatorialpress.com/article/ars/Volume%20072/volume-72-paper-5.pdf) ·
[Survey, §6.1.1](https://www.combinatorics.org/ojs/index.php/eljc/article/download/DS1/pdf/)

Every monochromatic neighborhood in a hypothetical counterexample has at most
16 vertices. The three-colorings on 15 and 16 vertices are classified, giving
small exact catalogues from which to work. The difficulty is making those
local neighborhoods coexist in one coloring of all 61 vertices. The project
supplies its own [Lean classification proofs and finite certificates](publication/CLASSIFICATION_PROVENANCE.md)
for these catalogues.

## Research process

The investigation moved repeatedly between structural mathematics, finite
enumeration, counterexample construction and SAT experiments. Early progress
on a favorable family was fast: a 973-input native search completed in
20.7 minutes of parallel wall time, using about 2.35 solver CPU-hours.
That tractable first branch established the value of exploiting classified
neighborhoods before asking a solver to explore the remaining coloring.

Most of the later computational difficulty concentrated around vertices with
color degrees `(14,14,16,16)`. Several approaches strengthened local
constraints or replaced neighborhoods with smaller catalogues, yet their
diagnostics repeatedly reached their limits without an answer. Counterexamples
to proposed shortcuts mattered as much as successful tests: a useful local
restriction was not automatically a complete reduction of the original
problem.

The eventual route combined two kinds of information. Exact overlap relations
made a highly constrained exceptional configuration finitely checkable.
A global count of incidences then connected that local work to an exhaustive
entrance into the remaining case. This reduced the final obstacle to 456
formulas retaining all 61 vertices, which both native solvers refuted.

The full account, including failed directions, measured costs and the role
of successive AI research prompts, is in [RESEARCH.md](RESEARCH.md).

## Search costs

The final decomposition has five possible sorted color-degree patterns,
introduced in [proof.md](proof.md): A = `(12,16,16,16)`,
B = `(13,15,16,16)`, C = `(14,14,16,16)`, D = `(14,15,15,16)` and
E = `(15,15,15,15)`. U and T name two critical neighborhood templates.
E is handled by the structural argument; A, B and D supply local inequalities
used in the final C reduction.

| Search phase | Required SAT inputs | Successful solver hours |
| --- | ---: | ---: |
| A | 360 | 0.84 |
| B | 5,096 | 21.36 |
| D / UUU | 679 | 1.96 |
| D / UUT | 679 | 1.73 |
| D / UTU | 6,576 | 18.90 |
| D / UTT | 6,576 | 18.92 |
| D / TTU | 18,204 | 61.88 |
| D / TTT | 18,204 | 62.02 |
| C | 456 | 1.54 |

These figures measure successful search time summed over solver processes,
excluding input generation, independent reruns and exploratory research.
Elapsed time depends on parallelism and host availability.
[Detailed phase accounting](publication/MEASURED_COSTS.md) ·
[Research history](RESEARCH.md)

The complete A/B/D rerun with CaDiCaL 3.0.1 used **246.81 solver CPU-hours**
and returned UNSAT for all **56,374** formulas, with no SAT, UNKNOWN or error
results. Its elapsed duration was **37h18m30s**, measured from launch to the
last solver finish rather than summed across solver processes.
Together with the existing two-solver C check, this corroborates every SAT
case in the proof. These verification costs are separate from the original
search times above.

## Proof

The human-readable argument is in [proof.md](proof.md). It begins by assuming
a four-coloring of the complete graph on 61 vertices with no monochromatic
triangle, then proceeds as follows:

1. **Restrict the vertex degrees.** Each of the four color degrees is at most
   16, and they sum to 60. There are exactly five possible sorted degree
   patterns.
2. **Establish local inequalities.** Exhaustive searches rule out specified
   rooted configurations in three of those patterns. A root means a chosen
   vertex together with its four colored neighborhoods. These results impose
   inequalities at every vertex of the relevant pattern.
3. **Use a global conservation identity.** Count incidences that are high at
   one endpoint, meaning color degree at least 15 in the color of that edge.
   Counting the same incidences from opposite ends forces either a suitable
   `(14,14,16,16)` root or synchronized endpoint behavior. Graph and degree
   arguments reduce the synchronized alternative to a parity contradiction
   or the guarded configuration excluded by the finite compatibility checks.
4. **Cover the remaining roots.** The critical-neighborhood classifications
   and exact overlap relations map every remaining counterexample to one of
   456 formulas on the full 61-vertex host.
5. **Apply the refutations.** Every formula in that final cover is UNSAT,
   contradicting the assignment that a counterexample would supply.

The correspondence between a coloring and a formula is essential. The proof
explains the coverage and coordinate changes; the computation supplies the
finite exclusions. The [dependency ledger](publication/DEPENDENCIES.json)
records the mathematical and computational premises separately.

## Verification method

This is a **computer-assisted proof using a complete mathematical reduction
formalized in Lean and native SAT solver results**. Lean proves that every
hypothetical counterexample gives a satisfying assignment to one of 56,830
explicitly defined formulas. The exhaustive covers, physical coordinate
changes, finite compatibility exclusions and encoding soundness are included
in that reduction.

The main theorem,
[`PricingIntegration.NativeWholeProof.ramsey61`](formal/src/PricingIntegration/NativeWholeProof.lean),
takes one computational premise, `AllNativeUnsat`, asserting that those concrete
formulas are unsatisfiable. Native solver results supply the evidence for this
premise. Every A/B/D and C formula has matching Kissat and CaDiCaL UNSAT
answers, bound to the same complete input hash. The
[A/B/D second-solver receipt](publication/checks/ABD_SECOND_SOLVER.json)
records the completed rerun; the C reconciliation is retained in the original
evidence archive.

[Exact input comparisons](formal/reproduce/README.md) connect the Lean-defined
formulas to retained or reconstructed DIMACS bytes and runner-recorded input
hashes. Native-result checks match those hashes to the solver records. These are
external checks, separate from the kernel-checked mathematical reduction.
[The verification method](publication/TRUST_AND_CERTIFICATION.md) and
[formal scope](publication/FORMALIZATION_STATUS.md) describe this boundary.

The [complete portable source build](formal/BUILD.md) passed from a fresh
checkout: all **1,809 modules**, including the 32 critical-neighborhood
classification modules and replay of their 55 small CNF/LRAT pairs. It used
**9.80 CPU-hours**, or **4h58m with two workers**, and reused no prior project
artifacts. The [build result](formal/BUILD_RESULT.json) records the pinned
compiler and dependencies; [RELEASE_CHECKS.md](publication/RELEASE_CHECKS.md)
indexes the mathematical and computational checks.

[CI](.github/workflows/verify.yml) checks all manifested mathematical sources and embedded data and builds a compact five-module physical-coloring target. The full
mathematical build has higher memory requirements. The measured workload
supports a recommendation of 64 GiB for serial checking or 128 GiB with
carefully controlled parallel jobs. The portable builder uses a fixed job
limit; it does not automatically adjust admissions to memory pressure.
[Measurements](formal/MEASUREMENTS.md) and the build guide give the details.

## AI assistance and responsibility

This research was heavily assisted by AI. GPT 5.6 in Codex with ultra reasoning
and Fable 5 in Claude Code with ultracode produced the initial A/B/D closures.
GPT-6 Astra in Codex with ultra reasoning developed the C-profile solution.
GPT-6 Pro research sessions contributed successive mathematical proposals
and reductions.

The mathematical reductions are verified in Lean, and every required SAT
instance has matching UNSAT results from Kissat and CaDiCaL. The work was
developed with extensive AI assistance and has not yet undergone independent
human review. The author takes responsibility for the result, its evidence
and corrections.
[Full attribution](publication/ATTRIBUTION.md)

## Reproduce the computations

The [reproduction guide](publication/REPRODUCIBILITY.md),
[Lean build guide](formal/BUILD.md) and
[formula-binding guide](formal/reproduce/README.md) separate these checks:

| Task | What it establishes |
| --- | --- |
| Authenticate and extract the evidence archive | Exact preserved files, manifests, native logs and recorded acceptance relationships |
| Reconstruct all 56,830 SAT input hashes | The original formula bytes are recoverable without writing hundreds of gigabytes of repeated data |
| Join reconstructed A/B/D formulas to native results | Every required formula matches its authenticated UNSAT record and solver log |
| Check the A/B/D second-solver evidence | Every required formula has a matching accepted CaDiCaL UNSAT result in addition to its original Kissat result |
| Build the complete Lean mathematical reduction | The implication from the explicit native UNSAT premise to the Ramsey bound |
| Compare Lean-defined formulas with retained or reconstructed inputs | Exact complete DIMACS identities for all 56,830 cases |
| Replay the 13,968 local compatibility checks | The retained finite witnesses still give the stated contradictions |
| Materialize and solve a chosen SAT input | A fresh native solver result for an exact case in the proof |

The Python reproduction tools use the standard library. The **375 MB original
evidence archive** and **246 MB A/B/D CaDiCaL archive** are stored with Git LFS.
Fetch both archives and authenticate the original:

```sh
git lfs install --local
git lfs pull --include='archives/*.tar.gz'
python3 -B reproduce/verify.py check
```

The [reproduction guide](publication/REPRODUCIBILITY.md) gives the extraction
and verification commands. The [second-solver checker](reproduce/abd_second_solver.py)
streams `archives/abd-cadical.tar.gz` without extracting it, using the original
snapshot to reconstruct and identify every input.

Every required input hash and both finite compatibility computations have
been checked using the portable tools. Archive authentication, clean-checkout
reproduction, Lean builds and formula-binding checks have separate receipts in
[RELEASE_CHECKS.md](publication/RELEASE_CHECKS.md).

The [cost table](publication/MEASURED_COSTS.md) states which search
attempts are included; it is not a total for every unsuccessful experiment.

## Repository layout

| Path | Purpose |
| --- | --- |
| [`proof.md`](proof.md) | Human-readable mathematical argument and explicit computational premises |
| [`RESEARCH.md`](RESEARCH.md) | Research narrative, failed approaches and measured costs |
| [`classification/`](classification/README.md) | Local critical-neighborhood proofs and their small certificate dependencies |
| [`formal/`](formal/README.md) | Complete mathematical reduction, pinned source package, build and formula-binding tools |
| [`reproduce/`](publication/REPRODUCIBILITY.md) | Portable archive, input and finite-computation checks |
| [`publication/`](publication/RELEASE_CHECKS.md) | Dependency ledger, verification status, references and computational records |
| `archives/evidence-v1.tar.gz` | Immutable evidence snapshot, tracked through Git LFS |
| `archives/abd-cadical.tar.gz` | Complete A/B/D CaDiCaL rerun evidence, tracked through Git LFS |
| [`.github/workflows/verify.yml`](.github/workflows/verify.yml) | Mathematical-source and data integrity, compact Lean build and supporting tool checks |

## Invitation to review

We welcome expert review of the mathematical argument and its correspondence
with the computational inputs. The proof, input reconstruction tools and
preserved results are supplied for that purpose.

## References

1. S. Fettes, R. L. Kramer and S. P. Radziszowski,
   [*An Upper Bound of 62 on the Classical Ramsey Number R(3,3,3,3)*](https://combinatorialpress.com/article/ars/Volume%20072/volume-72-paper-5.pdf),
   Ars Combinatoria 72 (2004), 41–63.
2. S. P. Radziszowski, [*Small Ramsey Numbers*, revision 18](https://doi.org/10.37236/21),
   April 24, 2026.
3. The [local classification proofs](publication/CLASSIFICATION_PROVENANCE.md)
   supply the critical-neighborhood results used here, with source and
   certificate provenance.
