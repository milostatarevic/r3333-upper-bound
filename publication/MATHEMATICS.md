# Mathematical verification map

The complete argument is [proof.md](../proof.md). The [Lean package](../formal/README.md) proves its reduction to **56,723 concrete CNFs**. Its endpoint, [`UniformK61.WholeProof.ramsey61`](../formal/src/UniformK61/WholeProof.lean), has one external computational premise: every formula in its explicit finite case type is unsatisfiable.

| Proof step | Mathematical argument and verification |
|---|---|
| Critical neighborhoods | Local K15/K16 completeness proofs and the [actual-host adapter](../formal/src/Ramsey61/ClassificationAdapter.lean); [classification provenance](CLASSIFICATION_PROVENANCE.md) |
| Degrees, profiles and tickets | The color-degree bounds, exhaustive profiles and double counting of incoming and outgoing tickets |
| Marked A/B/D roots | [CommonCover](../formal/src/UniformK61/CommonCover.lean) and [UUPhysicalCover](../formal/src/UniformK61/UUPhysicalCover.lean) give complete physical covers; [ABDProof.selector](../formal/src/UniformK61/ABDProof.lean) derives the strict ticket bounds from their exclusions |
| C entrances | [CEntrance.actual_C_cover](../formal/src/UniformK61/CEntranceFinal.lean) gives a direct 346-case marked-neighborhood cover, without a critical-template assumption on either 14-vertex root cell |
| Perfect balance | [BalancedStructure](../formal/src/UniformK61/BalancedStructurePair.lean) uses reciprocity, elementary connectivity, intersection bounds and parity to obtain one common high-color pair |
| Balanced hosts | [BalancedHost](../formal/src/UniformK61/BalancedHostOwners.lean) normalizes the two 16-neighborhoods to UU, UT or TT; [BalancedEncoding.actual_uniform_cover](../formal/src/UniformK61/BalancedEncodingActual.lean) supplies a satisfying valuation of the corresponding complete K61 formula |
| Composition and evidence | [WholeProof](../formal/src/UniformK61/WholeProof.lean) combines the branches; [input binding](../formal/reproduce/uniform/README.md) connects its concrete formulas to the native searches |

For marked neighborhoods, a normalized configuration consists of chosen support positions and one of the 600 cross-support words, together with all root, template and signed membership facts. The same finite coverage criterion applies to every retained list: each configuration reaches a case through a whole-host symmetry whose pulled-back target facts are recorded source facts.

Every physical transport acts on all 61 vertices and uses one global palette permutation. Template maps describe actual neighborhoods in that coloring. Their overlaps share the same physical edge variables. Marked-neighborhood membership is recorded in both directions, including negative units for omitted vertices.

## Notation and Lean names

A coloring is *good* when it has no monochromatic triangle. A color is *high* at a vertex when its degree there is at least 15.

- **H(v)** counts neighbors whose degree in the joining color is high at the neighbor. It is `highOwnNeighborCount c v` in Lean.
- **w(v)** sums the high color degrees at v itself. It is `criticalDegreeMass c v`, also equal to the cardinality of `incomingHighOwnSupport c v`.
- An **eligible C entrance** is a C-profile root with H(v) at least 32 and a low-colored neighbor that is high in their joining color. This is `CExteriorWitness`; the neighbor’s actual critical neighborhood supplies the mark used by the finite cover.
- **SelectorX** states the strict A/B/D ticket bounds. They are conclusions of the formal case covers and their computational exclusions.

Double counting of tickets, together with the A/B/D bounds, leaves either a C entrance or synchronized C/E profiles. The latter alternative forces every vertex to have the same named degree vector (16,16,14,14), after one global color relabeling.

## The finite computational boundary

| Part of the concrete case type | Formulas |
|---|---:|
| A | 360 |
| B | 5,096 |
| D | 50,918 |
| Direct C entrance cases | 346 |
| Balanced UU, UT and TT cases | 3 |
| **Total** | **56,723** |

`WholeProof.native_case_count` proves this total. The mathematical connection to each formula includes its complete physical constraints and, for balance, the auxiliary witnesses for support selectors and visible-neighborhood embeddings. No coverage, classification or encoding premise remains as a theorem parameter.

The [formal dependency map](../formal/MATHEMATICS.md) explains these constructions. The [verification method](TRUST_AND_CERTIFICATION.md) distinguishes the Lean reduction, the external byte-binding checks and the native UNSAT results. The [reproduction guide](REPRODUCIBILITY.md) gives their separate commands.
