# Critical catalogues on the 61-vertex host

[ClassificationAdapter.lean](Ramsey61/ClassificationAdapter.lean)
connects the proved K15/K16 catalogues to `Ramsey61.Host`. A
critical monochromatic neighborhood is mapped completely onto
its template, preserving actual vertices and one map of the
three remaining colors. The adapter also exposes the K15 extension
and the K16 strongly regular color-graph theorem.

The endpoints `physical_neighborhood_k15`,
`physical_neighborhood_k16` and `physical_high_neighborhood`
retain the actual vertex maps. They have no additional
catalogue-completeness premise and use only Lean's standard
`propext`, `Classical.choice` and `Quot.sound` axioms.
Fixed-palette normalization is supplied by
[FixedPhysicalNeighborhood.lean](../../formal/src/PricingIntegration/FixedPhysicalNeighborhood.lean),
using the proved template palette symmetries. These are coordinate
changes in the templates, not independent recolorings of shared
host edges.

The same adapter source is included as
[Ramsey61.ClassificationAdapter](../../formal/src/Ramsey61/ClassificationAdapter.lean)
in the complete mathematical build. Its maps supply the actual
critical neighborhoods in the A/B/D marked covers, the direct
C entrance cover and the balanced visible-neighborhood embeddings.
They enter the final theorem
[UniformK61.WholeProof.ramsey61](../../formal/src/UniformK61/WholeProof.lean).

Follow the [complete build instructions](../../formal/BUILD.md)
to compile the adapter with all dependencies, including the
classification sources and their 55 checked CNF/LRAT pairs.
The [source manifest](../../formal/SOURCE_MANIFEST.json) and
[build record](../../formal/BUILD_RESULT.json) identify the
accepted complete closure. The
[mathematical dependency map](../../formal/MATHEMATICS.md)
connects these classification endpoints to the full theorem.

GitHub CI checks source integrity and a small shared-encoding
target. Its scope does not include compiling this adapter or
replaying the classification traces.
