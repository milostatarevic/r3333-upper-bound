# Scope of the Lean verification

The [Lean source package](../formal/README.md) proves the complete mathematical reduction from a hypothetical good coloring of K61 to one of **56,723 explicitly defined SAT formulas**. The source includes classification completeness, exhaustive physical case covers, global counting, coordinate and palette transport, and encoding soundness.

The package pins Lean 4.32.1 and Mathlib `520045ab14e26149ee970e2e617ca04b09bde5d6`. The written argument is [proof.md](../proof.md); the [mathematical map](MATHEMATICS.md) connects its steps to the source.

## Exact theorem interface

Within `UniformK61.WholeProof`, the endpoint is:

```lean
abbrev Case := ABDProof.Case ⊕ (CEntrance.Case ⊕ BalancedHost.Owner)

def AllNativeUnsat : Prop :=
  ∀ k : Case, ¬∃ w : Valuation, FormulaSat w (formula k)

theorem ramsey61 (h : AllNativeUnsat) :
    ∀ c : Host, ¬NoMonochromaticTriangle c
```

`Host` is a four-coloring of the actual 61 vertices. `formula : Case → CNF` is a concrete definition. The [case-count theorem](../formal/src/UniformK61/WholeProof.lean) gives 56,374 A/B/D cases, 346 C cases and three balanced cases. The endpoint has no additional mathematical hypothesis about case coverage or formula correctness.

The theorem and case-count axiom audits permit only `propext`, `Classical.choice` and `Quot.sound`. This audit concerns the Lean proof; it does not discharge `AllNativeUnsat`.

## What the mathematical proof checks

The [marked covers](../formal/MATHEMATICS.md#marked-abd-and-c-covers) normalize the selected supports and their cross word. Their single finite coverage criterion checks that every target fact pulls back to a recorded source fact under one full-host symmetry. This includes complete signed marked-neighborhood membership. Whole-template symmetries preserve the actual overlaps. The direct C cover does not assume that a 14-vertex root cell extends to a critical coloring.

The [balanced reduction](../formal/MATHEMATICS.md#the-globally-balanced-case) proves the common high-color pair and the three normalized template owners. Actual opposite neighborhoods supply injective visible-template maps. Finite anchor and support catalogues cover these maps, and the encoding proof preserves every observed edge color. The support and embedding witnesses occupy disjoint auxiliary variable ranges, giving one satisfying valuation without changing any physical edge value.

The source closure includes 32 classification modules and 110 embedded data files, comprising 55 CNF/LRAT pairs. The classification proofs check these traces in Lean. [Classification provenance](CLASSIFICATION_PROVENANCE.md) describes their exact role.

## Exact inputs and external computations

The [binding driver](../formal/reproduce/uniform/README.md) uses a complete current-source build, audits the final theorem type and axioms, and emits every formula. External checkers compare ordered clauses, signs, dimensions and full DIMACS hashes with the native input catalogue. They cover the complete 56,723-case union, including all three balanced formulas and their auxiliary clauses.

Kissat 4.0.4 and CaDiCaL 3.0.1 provide matching UNSAT results for every required formula. Both use default options, with no CPU or wall-time cap. The release verifier joins all 113,446 required results to the exact input hashes. These native answers supply the theorem's computational premise. The large search refutations are not checked by the Lean kernel.

The [source manifest](../formal/SOURCE_MANIFEST.json), [complete build record](../formal/BUILD_RESULT.json) and [release checks](RELEASE_CHECKS.md) identify the source and evidence. A fresh complete build and a fresh input binding are separate operations. [CI](../.github/workflows/verify.yml) validates manifested source/data integrity and builds the small `UniformK61.CoreCounts` physical-base target; it does not rebuild the complete theorem, replay all classification traces, bind every input or rerun the searches.

The [build guide](../formal/BUILD.md), [formal measurements](../formal/MEASUREMENTS.md) and [verification method](TRUST_AND_CERTIFICATION.md) specify the reproduction and trust boundaries.
