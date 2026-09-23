# Verification record

Lean proves `PricingIntegration.NativeWholeProof.ramsey61` with the explicit computational premise `AllNativeUnsat`. The mathematical case coverage, preservation of the original coloring, coordinate and palette transport, classification use, and CNF encoding arguments are supplied by proved terms.

```lean
ramsey61 (h : AllNativeUnsat) (c : Ramsey61.Host) :
  ¬Ramsey61.NoMonochromaticTriangle c
```

The theorem and the exact case-count theorem report only `propext`, `Classical.choice`, and `Quot.sound` in their axiom audits. `AllNativeUnsat` remains visible as a theorem parameter; these audits do not check the large native search refutations.

| Check | Result |
|---|---|
| Clean mathematical source compilation | 1,777 modules passed |
| Established classification dependency | 32 previously checked modules, with source/data/artifact custody verified |
| Exact computational boundary, proved in Lean | 55,016 common cases + 1,358 UUU/UUT cases + 456 C cases = 56,830 |
| Final formula-to-input reproduction from the clean outputs | All 56,830 identities passed |
| Portable source/data/configuration manifest | All 1,809 modules and 110 embedded files passed static validation |

The [clean-build custody record](checks/clean_build/CLEAN_BUILD_CUSTODY.json) retains source, imported-artifact and output hashes and the original compiler receipts. Its final roots include both the whole theorem and `NativeWholeProof.native_case_count`. The [joined input-binding record](checks/joined_bindings/RUN_RESULT.json) connects that exact clean build to the native input identities; it runs no SAT solver. The computational evidence for UNSAT is retained in this repository's [search archive](../publication/REPRODUCIBILITY.md).

The established classification source and its 55 small CNF/LRAT pairs are included. The [classification custody record](checks/classification_baseline/CLASSIFICATION_BASELINE_CUSTODY_REVIEW_001.json) matches them to the retained earlier kernel-checked build. They were reused, without replay, during the clean mathematical run reported here. The portable full-source build command includes their replay; [BUILD.md](BUILD.md) describes its pinned Lean/Mathlib boundary. Its recorded execution covers the five-module CI target, not the complete 1,809-module closure.

The recorded 1,777-module build used the retained local controllers and a shared Mathlib installation. Its receipts bind project sources, imports and outputs but do not record the revision and hashes of all loaded Mathlib artifacts, including the additional `SimpleGraph.Bipartite` module. The dependency pins supplied for portable reproduction therefore describe the reproduction environment, not a complete attestation of that earlier dependency cache.

[MEASUREMENTS.md](MEASUREMENTS.md) reports CPU time, memory and storage. The package contains source, data, reproducible tools and records; compiled project artifacts and the separate native-search archive are not duplicated here.
