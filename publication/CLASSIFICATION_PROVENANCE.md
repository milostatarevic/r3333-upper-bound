# Provenance of the K15 and K16 classification

The proof uses the project's own derivation of the critical K15/K16
classification. Published accounts provide historical context; their theorem
statements or reported computations are not imported as axioms.

The K16 classification is historically due to Kalbfleisch and Stanton,
and the K15 classification to Heinrich. This attribution records the origin
of the structural results; the supplied local proofs and certificate data
establish the classifications used here.

## The mathematical endpoint

[CriticalCatalogues.lean](../formal/src/R4333Lean/CriticalCatalogues.lean)
contains two theorems without catalogue-completeness hypotheses:

- `R4333.k16CriticalCatalogue_complete`: every good three-coloring of K16
  is weakly isomorphic to one of the two literal templates.
- `R4333.k15CriticalCatalogue_complete`: every good three-coloring of K15
  is weakly isomorphic to the fixed deletion of one of those templates.

These prove that an arbitrary good coloring is represented. The K16 argument
uses the local common-neighbor certificate, constructive Clebsch uniqueness
and exhaustive 72-row complement classification. The K15 argument uses the
deficient-color certificate to extend an arbitrary good K15 to K16, then
applies completeness and the explicit deletion maps.

The importer [CheckedLRAT.lean](../formal/src/R4333Lean/CheckedLRAT.lean)
constructs ordinary Lean theorem declarations. It checks definitional equality
between the parsed CNF and the Lean-defined formula before submitting the
proof term to the kernel. Reading data in elaborator code does not add an
axiom asserting the computation's result.

## Sources and kernel verification

The [formal source package](../formal/README.md) includes the complete local
classification dependency closure: **32 modules and 55 CNF/LRAT pairs**.
[SOURCE_MANIFEST.json](../formal/SOURCE_MANIFEST.json) pins the mathematical
source and embedded data. Its SHA256 is
`15b6775769f3578acd5c6aa22c46506decb3c041bd98912a79d50dd6e55ea8ed`.
The standalone and integrated classification modules are byte-identical.
The [complete portable build](../formal/BUILD_RESULT.json) records successful
compilation of these exact sources on 23 September 2026.

The classification endpoints use only `propext`, `Classical.choice` and
`Quot.sound`.
The [standalone classification manifest](../classification/MANIFEST.json)
records the packaged source and certificate data and identifies the complete
portable build as their verification record.

The [complete portable build](../formal/BUILD_RESULT.json) compiled all
32 classification modules from source and replayed all 55 supplied pairs as
part of the 1,809-module mathematical closure. It used the pinned dependency
cache and its own project outputs, with no reused project artifacts.
[BUILD.md](../formal/BUILD.md) gives the reproduction commands.

## Connection to the K61 theorem

The integrated [ClassificationAdapter.lean](../formal/src/Ramsey61/ClassificationAdapter.lean)
supplies `physical_neighborhood_k15` and `physical_neighborhood_k16`, consumed
by [FixedPhysicalNeighborhood.lean](../formal/src/PricingIntegration/FixedPhysicalNeighborhood.lean).
For an actual neighborhood of size 15 or 16, respectively, these endpoints
supply an injective template-to-host map whose image is the entire
neighborhood, with a bijection onto the three remaining host colors. Their
mathematical premises are host goodness and the stated neighborhood size.

An individual catalogue map does not by itself establish compatibility on
overlaps. The complete Lean development proves those compatible-map,
owner/orbit, signed-suffix and encoding arguments separately, then consumes
them in [`NativeWholeProof.ramsey61`](../formal/src/PricingIntegration/NativeWholeProof.lean).
The [formal dependency map](../formal/MATHEMATICS.md) identifies the A/B/D,
C and G constructions. The final theorem has no additional classification or
mathematical coverage parameter: its explicit premise is `AllNativeUnsat`
over 56,830 concrete formulas.

The small classification certificates and the large native K61 searches have
different verification scopes. [Formula-binding checks](../formal/reproduce/README.md)
connect the Lean formulas to retained or reconstructed search inputs; their native UNSAT
answers supply external computational evidence. See
[FORMALIZATION_STATUS.md](FORMALIZATION_STATUS.md) for that boundary.

Routine CI validates the integrity of all manifested mathematical sources and embedded data and compiles
the five-module `PricingIntegration.NativeColoringClauses` dependency closure.
It does not replay classification certificates or compile the full theorem.
The full build has its separate commands and resource guidance in
[BUILD.md](../formal/BUILD.md) and the [reproduction guide](REPRODUCIBILITY.md).
