# Lean mathematics for R(3,3,3,3) ≤ 61

This package formalizes the mathematical reduction of the Ramsey bound to
56,830 explicitly defined finite SAT instances. Lean proves the exhaustive
case coverage, preservation of the original coloring through all reductions,
and the connection between the physical configurations and the exact CNFs.
The repository's [evidence archive](../publication/REPRODUCIBILITY.md) supplies the native
solver results and second-solver cross-checks.

The main theorem is
[`PricingIntegration.NativeWholeProof.ramsey61`](src/PricingIntegration/NativeWholeProof.lean).
Its computational premise is `AllNativeUnsat`, the unsatisfiability of the
concrete formulas indexed by its finite `Case` type. No mathematical coverage,
classification, transport or encoding hypothesis remains in that theorem.
Its axiom audit contains `propext`, `Classical.choice` and `Quot.sound`.

| Computational family | Indexed cases |
|---|---:|
| Common A/B and four mixed D owners | 55,016 |
| Original D/UUU and D/UUT families | 1,358 |
| C family | 456 |
| **Total** | **56,830** |

[`NativeWholeProof.native_case_count`](src/PricingIntegration/NativeWholeCount.lean)
proves the total in Lean. [The mathematical dependency map](MATHEMATICS.md)
explains the constructions and their interfaces. The repository's
[human-readable proof](../proof.md) defines the degree-profile names and the
overall argument.

The source closure includes the project's K15/K16 classification library and
its 55 small CNF/LRAT pairs. The [complete portable build](BUILD_RESULT.json)
passed for all 1,809 modules from a fresh checkout and checked those traces
inside Lean, without prior project artifacts. Native SAT exclusions for the
56,830 final instances are supported
by the archived searches and exact formula-to-input bindings.

The package pins Lean 4.32.1 and Mathlib revision
`520045ab14e26149ee970e2e617ca04b09bde5d6`.
`SOURCE_MANIFEST.json` records every mathematical source and embedded data file.
No compiled artifacts or solver binaries are part of the source package.

Build and input-binding reproduction instructions are in [BUILD.md](BUILD.md) and
[reproduce/README.md](reproduce/README.md). The three operations are separate: checking the Lean
mathematics, verifying exact input identities, and rerunning the native searches.
The input-identity tools invoke no SAT solver.

The [verification record](VERIFICATION.md) and [resource measurements](MEASUREMENTS.md) describe the checked build and reproducibility costs.
