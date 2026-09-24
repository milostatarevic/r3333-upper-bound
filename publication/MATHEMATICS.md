# Mathematical verification map

The complete written argument is [proof.md](../proof.md). The
[Lean package](../formal/README.md) proves its mathematical reduction to
**56,830 concrete CNFs**. Its endpoint,
[`PricingIntegration.NativeWholeProof.ramsey61`](../formal/src/PricingIntegration/NativeWholeProof.lean),
has the single computational premise `AllNativeUnsat`: every formula in its
explicit finite `Case` type is unsatisfiable. Classification, case coverage,
physical transport and encoding soundness are proved in the source.

| Proof step | Mathematical argument and verification |
|---|---|
| Critical neighborhoods (§1) | Local K15/K16 completeness proofs and the [actual-host adapter](../formal/src/Ramsey61/ClassificationAdapter.lean); [classification provenance](CLASSIFICATION_PROVENANCE.md) |
| Degrees, incidence and A/B/D selectors (§§2–3) | The [A/B/D evidence index](ABD_EVIDENCE_INDEX.md), [D specification](D_COVER_AND_ENCODING.md), and formal physical covers, native prefixes and signed suffixes |
| Local relation and guarded exclusion (§§4–5) | Formal structural reductions and both exhaustive G covers; `GComplete.guarded_G_exclusion` has no native SAT premise. The [finite replay tools](REPRODUCIBILITY.md#5-replay-the-local-relation-and-g-exclusions) provide a separate check |
| Global entrance (§6) | Formal incidence synchronization, low-set counting, uniformity and construction of the actual regular-overlap guard |
| Physical C cover and formula semantics (§§7–8) | The formal 456-seed cover and satisfying valuation for each reached concrete formula, including its signed seed literals and auxiliaries |
| Composition (§9) | The main theorem supplies all mathematical components and derives the contradiction from `AllNativeUnsat`; [formal dependency map](../formal/MATHEMATICS.md) |
| Verification (§10) | [Native trust standard](TRUST_AND_CERTIFICATION.md), [check records](RELEASE_CHECKS.md), and [formalization status](FORMALIZATION_STATUS.md) |

## Notation and Lean names

A coloring is good when it has no monochromatic triangle. An incidence is
high when its vertex's degree in that edge's color is at least 15.

- **H(v)** counts neighbors whose degree in the joining color is high at the
  neighbor. It is `highOwnNeighborCount c v` in the Lean source.
- **W(v)** sums the high color degrees at v itself. It is
  `criticalDegreeMass c v`, also equal to the cardinality of
  `incomingHighOwnSupport c v`.
- An **eligible C root** has profile (14,14,16,16) and H(v) at least 32.
- **Selector-X** denotes the A/B/D incidence bounds obtained from their
  formal exhaustive covers and native computational exclusions.
- **G** is the exact regular-overlap configuration in §5. It occurs inside
  the global entrance argument; the final 456 formulas do not assume G.

## Follow a computational premise

The [case-count theorem](../formal/src/PricingIntegration/NativeWholeCount.lean)
proves the partition 55,016 common A/B/mixed-D cases, 1,358 original UUU/UUT
cases and 456 C cases. The family is defined in Lean rather than supplied as
an abstract theorem parameter.

The [formula-binding tools](../formal/reproduce/README.md) compare the
Lean-defined formulas with retained or reconstructed formula bytes, whose
SHA-256 values are matched to runner-recorded input hashes. Those external
checks, and the native UNSAT records themselves, remain separate from
the Lean proof. The main theorem does not kernel-check the large SAT
refutations. The 55 smaller classification CNF/LRAT pairs have their own
kernel-checked role.

Every formula has matching UNSAT answers from Kissat and CaDiCaL. The
[A/B/D second-solver receipt](checks/ABD_SECOND_SOLVER.json) covers all 56,374
original A/B/D cases; the original archive retains the corresponding
two-solver reconciliation for all 456 C cases.

For A/B/D, the [evidence index](ABD_EVIDENCE_INDEX.md) identifies the finite
data, complete censuses, formula assets and native results. For C and G,
[Appendix A](../proof.md#appendix-a-portable-evidence-locators) locates the
archive members. The [reproduction guide](REPRODUCIBILITY.md) separates
archive authentication, exact input reconstruction, formal builds, input
bindings and fresh native searches.
