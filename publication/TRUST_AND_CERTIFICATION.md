# Verification method

We give a computer-assisted proof of R(3,3,3,3) ≤ 61. The release consists of
the complete written argument, Lean mathematical reduction, exhaustive case
covers, exact formula reconstruction, native solver results and reproducible
finite checks. These
are the mathematical and computational basis of the claimed bound.

## The verification standard used here

The written proof and the Lean development establish that any counterexample
gives a satisfying assignment to one of the searched formulas. The formal
reduction includes the exhaustive covers and the 13,968 finite compatibility
exclusions used for the separate guarded branch. The computation supplies
native UNSAT results for all **56,830 SAT formulas**.

The main theorem,
[`NativeWholeProof.ramsey61`](../formal/src/PricingIntegration/NativeWholeProof.lean),
takes only `AllNativeUnsat`, which asserts unsatisfiability of its concrete
finite CNF family. All physical extraction, coverage, transport and encoding
implications are proved within the mathematical development.

The computational conclusion uses explicit trust in native solver answers.
Kissat and CaDiCaL agree on all 456 full-host C formulas. The A/B/D evidence
supplies the retained Kissat results. Input reconstruction and native-result
accounting connect each required formula's SHA-256 to its runner-recorded
input hash and UNSAT result.

The verification boundary has three parts:

- **The mathematical statement and Lean kernel:** the definitions describe
  the physical coloring problem, and the kernel checks the reduction and
  finite mathematical exclusions.
- **Formula binding and evidence accounting:** external tools compare the
  complete Lean-emitted formulas with retained or reconstructed DIMACS bytes.
  Native-result accounting then joins the formula hashes to the required case
  census and the runner-recorded input hashes and UNSAT results.
- **The native searches:** each solver's UNSAT result is accepted as the
  exclusion of its exact formula. The large K61 refutations are not
  kernel-checked certificates.

Hashes establish file identity. The byte-binding tools and the native answers
supply evidence for the theorem's explicit computational premise; they are
not replaced by its axiom audit. The
[reproduction guide](REPRODUCIBILITY.md), [Lean build guide](../formal/BUILD.md)
and [formula-binding guide](../formal/reproduce/README.md) give the separate
verification commands.

## Comparison with the earlier bound

Fettes, Kramer and Radziszowski present a mathematical reduction and exhaustive
computations in their [2004 paper, §§5–6](https://combinatorialpress.com/article/ars/Volume%20072/volume-72-paper-5.pdf).
They report that the first and third authors independently obtained and compared
all computational results in §5, with no discrepancies. Their final exclusion
was obtained by both programs. This is a relevant precedent for a computational
proof supported by explicit algorithms.

The present repository uses SAT encodings and records its own verification
scope: the complete C family has independent Kissat/CaDiCaL agreement. The
A/B/D evidence supplies the original native runs without a full second-solver
replay. The Lean reduction and native result checks have distinct scopes. The two projects therefore
share a general computational-proof methodology, with different verification
coverage documented explicitly.

## Formal mathematics and exact input identities

The [`formal/` package](../formal/README.md) supplies the complete mathematical
source closure. Its final case type contains 55,016 common A/B/mixed-D
formulas, 1,358 UUU/UUT formulas and 456 C formulas. The total of 56,830 is
proved by [NativeWholeCount](../formal/src/PricingIntegration/NativeWholeCount.lean).
[FORMALIZATION_STATUS.md](FORMALIZATION_STATUS.md) gives the theorem interface
and the implementation of each reduction.

The source closure includes the project's K15/K16 classification proofs and
55 small CNF/LRAT pairs. Those certificates establish completeness of the
critical-neighborhood catalogues. The
[complete portable build](../formal/BUILD_RESULT.json) compiled all 1,809 modules,
including the 32 classification modules, and replayed the supplied traces.
It used a fresh checkout, pinned dependencies and its own project outputs;
no prior project artifacts were reused.
[Classification provenance](CLASSIFICATION_PROVENANCE.md) identifies the
classification sources, payloads and checks.

Complete input comparisons cover every formula in the final case type,
including the deterministic bases and each ordered signed suffix. Their
scope is exact byte identity with the retained or reconstructed formulas,
established by the external tools in
[formal/reproduce/](../formal/reproduce/README.md). Full per-case A/B/D CNFs
are not archived: their retained bases and suffix data reconstruct formulas
whose SHA-256 values match the solver runners' recorded input hashes.
Native-result accounting checks those hashes against the accepted results.
This is distinct from a kernel-checked DIMACS parser or a checked refutation
of each large formula.

The compact CI job checks manifested mathematical-source and data integrity and the five-module
physical-coloring target. The complete mathematical build and its theorem
and axiom audit have separate records in [RELEASE_CHECKS.md](RELEASE_CHECKS.md).

## Costs and responsibility

Native search timings and their accounting boundaries are in
[the cost table](MEASURED_COSTS.md). Reproduction and formal
check receipts are listed in [RELEASE_CHECKS.md](RELEASE_CHECKS.md).

The proof was heavily assisted by AI and has not yet been independently
verified by a human, including its human author. The author takes responsibility
for the result, its evidence and corrections; see
[ATTRIBUTION.md](ATTRIBUTION.md).
