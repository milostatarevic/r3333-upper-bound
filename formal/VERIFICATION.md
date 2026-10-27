# Verification boundary and records

The verification has three parts: checking the Lean mathematics, matching the exact formulas to native inputs, and checking the retained native solver records. Each part has its own execution record.

## Mathematical source build

[`SOURCE_MANIFEST.json`](SOURCE_MANIFEST.json) pins all selected project modules, 110 embedded classification files, and build controls. The portable builder compiles the complete selected closure with the pinned Lean/Mathlib environment. Project imports resolve to that run's own library, and the build includes replay of the 55 small classification CNF/LRAT pairs.

[`BUILD_RESULT.json`](BUILD_RESULT.json) identifies the recorded run. Detailed module receipts identify each source, compiler command, imported artifact, output artifact, log, exit status and resource measurement. A successful complete build has no failed or pending modules and no reused project artifacts. Source validation alone, a partial target, and the complete build are distinct operations.

The final theorem is:

```lean
UniformK61.WholeProof.ramsey61 (h : AllNativeUnsat) :
  ∀ c : Ramsey61.Host, ¬Ramsey61.NoMonochromaticTriangle c
```

`AllNativeUnsat` concerns exactly 56,723 formulas. The theorem and case-count audits permit only `propext`, `Classical.choice` and `Quot.sound`. The native UNSAT premise is an explicit theorem parameter.

## Exact formula binding

The [binding driver](reproduce/uniform/README.md) accepts a successful complete current-source build. It checks the exact final theorem type and case count, runs four Lean emitters against that build, and compares the entire disjoint input catalogue. The checks cover ordered literals, signs, dimensions, byte counts and full DIMACS hashes.

Its `RUN_RESULT.json` retains source, compiler, runtime and build identities. Inputs, logs, sources and artifacts are checked before and after the execution. The shared caches used by the common and balanced emitters have Lean proofs of exact ordered-formula equality. Serialization, runtime execution and hash comparison remain external operational checks.

## Native evidence and the release package

The native boundary has 56,723 cases and two solver records per case, for 113,446 required runs. The verification policy uses Kissat 4.0.4 and CaDiCaL 3.0.1 with default options and no CPU or wall-time cap. A case contributes to the exclusion only when the retained input, command, binary, raw log and exit status agree on UNSAT. SAT, UNKNOWN, errors and missing records do not count as exclusions.

The release package joins this exact native boundary to the source build and fresh binding. Its `RELEASE.json` identifies the records under `math/build/`, `math/binding/`, and the native input and result directories. The current repository's `reproduce/uniform_release.py verify-package` checks the complete package, including its theorem audit, formula identities and all selected native records. It does not launch Lean or a SAT solver.

The final native UNSAT results remain external to the Lean kernel. The included classification certificates, mathematical reductions and exact formula definitions are checked inside Lean; the standard compiler and pinned dependency runtime remain part of that checking environment.

Reproduction commands are in [BUILD.md](BUILD.md) and [reproduce/README.md](reproduce/README.md).
