# Verification record

Lean proves `PricingIntegration.NativeWholeProof.ramsey61` with the explicit
computational premise `AllNativeUnsat`. The mathematical case coverage,
preservation of the original coloring, coordinate and palette transport,
classification use, and CNF encoding arguments are supplied by proved terms.

```lean
ramsey61 (h : AllNativeUnsat) (c : Ramsey61.Host) :
  ¬Ramsey61.NoMonochromaticTriangle c
```

The theorem and the exact case-count theorem report only `propext`,
`Classical.choice` and `Quot.sound` in their axiom audits. `AllNativeUnsat`
remains visible as a theorem parameter; these audits do not check the large
native search refutations.

| Check | Result |
|---|---|
| Complete portable source build | All 1,809 modules passed from a fresh checkout; no prior project artifacts reused |
| Classification proofs | All 32 modules compiled from source and all 55 small CNF/LRAT pairs replayed inside Lean |
| Exact computational boundary, proved in Lean | 55,016 common cases + 1,358 UUU/UUT cases + 456 C cases = 56,830 |
| Separate exact input binding | All 56,830 formula-to-input identities passed |
| Source and data validation | All 1,809 modules and 110 embedded files match the source manifest |

The [build result](BUILD_RESULT.json) records the complete portable execution
for [SOURCE_MANIFEST.json](SOURCE_MANIFEST.json), SHA-256
`15b6775769f3578acd5c6aa22c46506decb3c041bd98912a79d50dd6e55ea8ed`.
The [compressed build records](checks/portable-build.tar.gz) contain the
per-module compiler receipts and logs, without compiled objects.
The build used Lean 4.32.1 and the nine package revisions pinned by
`lake-manifest.json`, including Mathlib
`520045ab14e26149ee970e2e617ca04b09bde5d6`. The run records source, imported-artifact
and output hashes. Project imports resolve only to the run's own library;
external imports resolve to the fresh dependency cache and toolchain.
The standard cached dependency binaries remain part of the Lean/Mathlib
trust boundary.

The [joined input-binding record](checks/joined_bindings/RUN_RESULT.json)
separately connects the Lean-defined formulas to the native input identities.
That check was not rerun as part of the portable compilation. The native
UNSAT evidence and second-solver cross-checks are described in this repository's
[search reproduction guide](../publication/REPRODUCIBILITY.md). All 56,374 A/B/D
inputs and all 456 C inputs have UNSAT results from both solvers. These results
support `AllNativeUnsat`; their large refutations are not checked inside Lean.

[BUILD.md](BUILD.md) gives the reproduction commands.
[MEASUREMENTS.md](MEASUREMENTS.md) reports CPU time, memory and storage.
Compiled project artifacts are not included in the source package.
