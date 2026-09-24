# Mathematical verification map

The [Lean source package](../formal/README.md) proves the complete mathematical
reduction from a hypothetical good coloring of K61 to one of 56,830 concrete
SAT formulas. It includes exhaustive physical case covers, coordinate and
palette transport, the finite G exclusions, and complete encoding soundness.
Its sole computational premise is that the explicitly defined formulas are
unsatisfiable.

The package pins Lean 4.32.1 and Mathlib
`520045ab14e26149ee970e2e617ca04b09bde5d6`. The written argument is
[proof.md](../proof.md); the [formal dependency map](../formal/MATHEMATICS.md)
connects its constructions to the checked declarations.

## Verification by proof step

| Written proof step | Lean implementation |
|---|---|
| §1: critical K15/K16 classification and extension | Local completeness proofs with the 55 small CNF/LRAT pairs; [ClassificationAdapter](../formal/src/Ramsey61/ClassificationAdapter.lean) supplies physical neighborhood and palette maps |
| §2: degrees and incidence | Degree bounds, exhaustive profiles, actual high-incidence supports and the H/W identity |
| §3: A/B/D supplied-root exclusions | [ActualProfileCover](../formal/src/CompletionC/ActualProfileCover.lean) and [UUQExactNative](../formal/src/PricingG/UUQExactNative.lean) connect actual roots to exhaustive native formula families, including the full prefixes and signed suffixes |
| §§4–5: local completion and guarded G | Structural classification, physical core coverage and finite contradictions are combined by [GComplete](../formal/src/PricingIntegration/GComplete.lean); this exclusion takes no native UNSAT premise |
| §6: global entrance | Incidence synchronization, dense bipartiteness, low-set counting, parity and the uniform-host-to-G construction yield a C exterior witness using the proved selector and G exclusion |
| §§7–8: C cover and encoding | [CComplete](../formal/src/PricingIntegration/CComplete.lean) proves the compatible 456-seed cover and supplies a satisfying valuation of its exact [concrete family](../formal/src/Ramsey61/CConcreteFamily.lean) |
| §9: composition | [NativeWholeProof.ramsey61](../formal/src/PricingIntegration/NativeWholeProof.lean) composes these implications with the explicit native UNSAT premise |

## Exact theorem interface

```lean
PricingIntegration.NativeWholeProof.ramsey61
  (h : AllNativeUnsat) : ∀ c : Host, ¬NoMonochromaticTriangle c
```

`Host` is a four-coloring of the actual 61 vertices. The finite type `Case`
and function `formula : Case → CNF` are concrete definitions.
`AllNativeUnsat` is `∀ k : Case, ¬Satisfiable (formula k)`.

| Part of `Case` | Formulas |
|---|---:|
| Common A/B and mixed-D owners | 55,016 |
| Original D/UUU and D/UUT owners | 1,358 |
| C family | 456 |
| **Total** | **56,830** |

[NativeWholeCount](../formal/src/PricingIntegration/NativeWholeCount.lean)
proves this total. The endpoint supplies the A/B/D selector, guarded-G
exclusion and physical C-to-CNF cover to its outer composition theorem.
It has no additional mathematical coverage, classification, transport or
encoding parameter.

The native UNSAT results remain external evidence for `AllNativeUnsat`.
Kissat and CaDiCaL agree on all 56,830 formulas, including the complete
[A/B/D second-solver rerun](checks/ABD_SECOND_SOLVER.json).
The endpoint's audited axioms are `propext`, `Classical.choice` and
`Quot.sound`; this axiom list does not discharge the explicit computational
premise. The large K61 search refutations are not checked by Lean.

## Exact input binding

The [formula-binding tools](../formal/reproduce/README.md) compare complete
Lean-emitted inputs with retained or reconstructed formula bytes: DIMACS
headers, clause order, signs, suffixes, dimensions and full formula hashes.
The latter are matched to runner-recorded input hashes and UNSAT results. The checks cover
all 55,016 common, 1,358 UUU/UUT and 456 C cases. The UUU and UUT formulas
retain their separate native identities.

These byte comparisons are external checks, not a Lean theorem about parsing
archived DIMACS files. They connect the formal reduction's formulas to the
native computation used by the computer-assisted proof. The
[verification method](TRUST_AND_CERTIFICATION.md) states the complete trust
boundary, and [RELEASE_CHECKS.md](RELEASE_CHECKS.md) indexes the binding,
build and theorem-audit records.

## Build and classification scope

The [source manifest](../formal/SOURCE_MANIFEST.json) identifies the exact
mathematical source and embedded data accepted by the
[complete portable build](../formal/BUILD_RESULT.json). All 1,809 modules were
compiled from a fresh checkout into an isolated output tree. The run records
the compiler identity, all pinned dependency revisions and imported-artifact
hashes; no prior project artifacts were reused.

The build includes all 32 classification modules and replays all 55 supplied
small CNF/LRAT pairs. [Classification provenance](CLASSIFICATION_PROVENANCE.md)
describes their role. This operation is separate from rerunning the large
native searches. The [measured workload](../formal/MEASUREMENTS.md)
supports a recommendation of 64 GiB for serial checking or 128 GiB with
carefully controlled parallel jobs. These are hardware recommendations,
not implemented build profiles: the portable builder has a fixed job limit.
The build guide gives the commands.

[CI](../.github/workflows/verify.yml) validates all manifested mathematical sources and embedded data and compiles the five-module closure of
`PricingIntegration.NativeColoringClauses`. That compact target checks the
physical-coloring foundations. Full mathematical build acceptance is recorded
separately in the release checks.

The complete proof has not yet been independently verified by a human. Its written mathematics,
Lean source and computational evidence are supplied for that review.
