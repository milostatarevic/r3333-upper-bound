# Provenance of the K15 and K16 classification

The proof uses the project's own derivation of the critical K15/K16 classification. Published accounts provide historical context; their theorem statements or reported computations are not imported as axioms.

The K16 classification is historically due to Kalbfleisch and Stanton, and the K15 classification to Heinrich. This attribution records the origin of the structural results. The supplied local proofs and certificate data establish the classifications used here.

## Mathematical endpoints

[CriticalCatalogues.lean](../formal/src/R4333Lean/CriticalCatalogues.lean) contains two theorems without catalogue-completeness hypotheses:

- `R4333.k16CriticalCatalogue_complete`: every good three-coloring of K16 is weakly isomorphic to one of the two literal templates.
- `R4333.k15CriticalCatalogue_complete`: every good three-coloring of K15 is weakly isomorphic to the fixed deletion of one of those templates.

The K16 argument uses the local common-neighbor certificate, constructive Clebsch uniqueness and the exhaustive 72-row complement classification. The K15 argument uses the deficient-color certificate to extend an arbitrary good K15 to K16, then applies completeness and the explicit deletion maps.

The importer [CheckedLRAT.lean](../formal/src/R4333Lean/CheckedLRAT.lean) constructs ordinary Lean theorem declarations. It checks definitional equality between the parsed CNF and the Lean-defined formula before submitting the proof term to the kernel. Reading the data in elaborator code does not add an axiom asserting the computation's result.

## Sources and certificate checking

The [formal source package](../formal/README.md) contains the classification
dependency closure: **32 modules and 55 CNF/LRAT pairs**. The 110 payload files
occupy 5,081,743 bytes. They are included with the selected mathematical sources
and retain their authenticated contents.

The [source manifest](../formal/SOURCE_MANIFEST.json) identifies the source and
data files. A complete source build compiles the classification modules and
replays all 55 pairs. The [source index](../formal/SOURCE_INDEX.json) connects
the public modules to the accepted formal capsule; its raw build records and
classification logs are retained as evidence.

The classification endpoints use only `propext`, `Classical.choice` and
`Quot.sound`. The [reproduction guide](../REPRODUCIBILITY.md) provides the
commands for checking the sources and traces.

## Connection to the K60 theorem

[ClassificationAdapter.lean](../formal/src/UniformK60/ClassificationAdapter.lean)
supplies `physical_neighborhood_k15` and `physical_neighborhood_k16`. For an
actual neighborhood of size 15 or 16, these theorems give an injective
template-to-host map whose image is the entire neighborhood, with a bijection
onto the three remaining host colors. Their mathematical premises are host
goodness and the stated neighborhood size.

An individual catalogue map does not by itself establish compatibility on
overlaps. The marked-cover and balanced-encoding developments prove those
physical transport and encoding arguments separately. They preserve all
shared edges and use a single global palette. The
[formal theorem map](../proof.md#9-formal-theorem-and-computational-boundary)
identifies the corresponding constructions.

The final theorem,
[`UniformK60.ramsey60_of_exact_unsat`](../formal/src/UniformK60/FiniteBoundary.lean),
has no additional classification or mathematical coverage parameter. Its
explicit external premise is unsatisfiability of 296,797 concrete formulas.
The [input-binding checks](../REPRODUCIBILITY.md#rebuild-and-bind-the-formal-definitions)
connect these formulas to the native searches; those answers have a different
verification scope from the kernel-checked classification traces.
