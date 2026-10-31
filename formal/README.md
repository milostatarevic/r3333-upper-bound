# Lean mathematics for R(3,3,3,3) ≤ 60

This package formalizes the mathematical reduction to **296,797 explicitly
defined SAT formulas**. Lean proves exhaustive case coverage, preservation of
one physical coloring under the coordinate changes, and satisfaction of the
corresponding formulas by any hypothetical coloring without a monochromatic
triangle.

The endpoint is
[`UniformK60.ramsey60_of_exact_unsat`](src/UniformK60/FiniteBoundary.lean):

```lean
ramsey60_of_exact_unsat (h : ExactInputs.AllUnsat) :
  ∀ c : Host, ¬NoMonochromaticTriangle c
```

`Host` is an ordinary four-coloring of the edges on 60 vertices. The sole
external premise, `ExactInputs.AllUnsat`, states that none of the indexed
formulas has a satisfying valuation. No classification, case-coverage,
transport or encoding assumption remains as a theorem parameter. The theorem's
axiom audit contains only `propext`, `Classical.choice` and `Quot.sound`.

| Formula family | Cases |
|---|---:|
| A | 360 |
| B | 5,096 |
| D | 50,918 |
| E | 231,168 |
| C1 entrances | 692 |
| C2 entrances | 7,840 |
| All-five guards | 3 |
| Mixed marked balance | 720 |
| **Total** | **296,797** |

Every formula uses the same 7,080 physical edge-color variables and the same
149,270-clause good-coloring base on K60. Marked and entrance formulas add
signed facts. Balanced formulas additionally describe degree bounds, supports
and visible critical-neighborhood embeddings.

The public package contains every selected source module and the 110 embedded
classification files. A complete build replays the 55 small CNF/LRAT pairs
inside Lean. The large native UNSAT results are external computational
evidence; exact-input checks connect their DIMACS bytes to the formal
formulas.

[SOURCE_MANIFEST.json](SOURCE_MANIFEST.json) pins the source, configuration and
data closure for the public build. [SOURCE_INDEX.json](SOURCE_INDEX.json)
connects those mathematical source files to the formal evidence capsule.
Module namespaces and source bytes are retained unchanged.

Lean 4.32.1 and the Mathlib revision
`520045ab14e26149ee970e2e617ca04b09bde5d6` are pinned. Follow [BUILD.md](BUILD.md) for a fresh source build and
[the reproduction guide](../REPRODUCIBILITY.md) for the four exact-input
comparisons in the canonical capsule workspace.
The two workflows retain their own build receipts; a source-only build does
not run the native searches or substitute for the input comparisons.

The mathematical exposition and theorem map are in [proof.md](../proof.md).
[Classification provenance](../publication/CLASSIFICATION_PROVENANCE.md)
describes the small checked traces. The [release index](../publication/checks/K60_RELEASE.json)
identifies the accepted formal and native evidence.
