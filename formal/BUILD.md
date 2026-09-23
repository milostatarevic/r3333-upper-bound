# Build the mathematical proof from source

This package contains the complete Lean source dependency closure, the existing small classification proof traces, and a pinned Lean/Mathlib configuration. It does not contain compiled project modules. The final theorem takes the explicitly indexed native SAT exclusions as its computational premise; building the mathematics does not rerun those searches.

Install Python 3.10 or newer, Git, and Lean's `elan` toolchain manager. From this directory, let Lake obtain the dependencies pinned by `lake-manifest.json` and their matching Mathlib cache:

```sh
lake exe cache get
lake build Mathlib.Combinatorics.SimpleGraph.Bipartite
lake env python3 build.py --validate-only
lake env python3 build.py --jobs 1
```

Keep the supplied lock file. Do not run `lake update`: changing the dependency revisions invalidates this package's pins. No additional Python packages are required. The compiler must match `lean-toolchain`; the builder verifies each dependency checkout against the locked Git revision and rejects tracked modifications.

The default build includes the complete root dependency closure, including the 32 existing classification source modules and their 55 small proof traces. Those classification checks are actual replay work. The local clean mathematical validation described in the accompanying receipts reused a separately checked classification baseline instead; it must not be represented as a new source-only replay. This portable builder has no baseline-import mode.

For a smaller build that cannot replay certificates:

```sh
lake env python3 build.py --target PricingIntegration.NativeColoringClauses --no-certificate-replay --jobs 1
```

A target includes all its project dependencies. `--no-certificate-replay` fails before launching Lean if any selected source contains a `checked_lrat_proof`, `lrat_proof`, or `lrat` command. It does not silently omit those modules or replace their theorems. `--validate-only` checks the package's source/configuration hashes, imports, embedded files, and selected dependency graph without compiling or replaying anything.

Choose `--jobs` from 1 through 8. Each compiler is single-threaded (`-j1`). The driver imposes no artificial time or memory limit. A job count is a concurrency ceiling, not a memory guarantee: some finite checks use substantially more memory than ordinary modules. Start with one job and use the supplied clean-build measurements to select higher concurrency for the available memory. This package does not infer a whole-build ETA from a small smoke test.

Every invocation creates a fresh `.build/runs/<timestamp>_<id>/` directory. Accepted outputs go into that run's single `lib/` namespace; prior project artifacts and ambient `LEAN_PATH` project outputs are excluded. Each module retains its source hash, exact compiler command, compiler hash, direct imported artifact hashes, exit status, log, and elapsed time in an immutable receipt. On macOS/Linux, receipts also contain the process's CPU time and peak RSS; on platforms without `wait4`, those two fields are unavailable. `BUILD_RESULT.json` records the final target/closure status. An error stops new admissions and allows already active compiler processes to finish; an interrupted or partial run is never reported as PASS. A retry creates a new run rather than changing old receipts.

The manifest pins all project source and embedded data. The builder checks those pins before compiling, checks each module and its imported artifacts again at completion, and rechecks the full package at the end. External Lean/Mathlib dependencies remain the pinned standard toolchain and package trust boundary; this is not a reproducible-build attestation for their cached binaries. Compiling the final theorem establishes its mathematical reduction to the stated native SAT premise. The separate input-reproduction checks bind those formulas to the retained native solver results, which support the unsatisfiability premise.
