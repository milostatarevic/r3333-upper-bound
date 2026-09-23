# Formalization and reproduction measurements

The complete mathematical build and the joined exact-input checks passed
on 22 September 2026. The theorem's finite computational boundary contains
56,830 explicitly defined CNFs. These measurements cover formalization and
deterministic input verification; the original SAT searches were not rerun.

| Completed operation | Measured CPU | Scope |
|---|---:|---|
| Clean mathematical rebuild | **12.263 CPU-hours** | 1,777 modules compiled; 32 previously checked classification modules reused |
| Joined portable input reproduction and comparison | **142.98 CPU-seconds** | All 56,830 complete original input identities matched |

The clean compiler span was **2h31m23s**, from the first compiler admission
to the final module, with parallel workers and a controller restart. The
accepted compiled artifacts total **2.101 GB (1.957 GiB)**. Eleven initial
namespace failures, costing **2.87 CPU-seconds**, are preserved separately;
the complete source/output/import-hash custody check passed. This build
reuses pinned Lean/Mathlib and the established classification library. The
classification library's separate recorded rebuild cost is 827.71 CPU-seconds.

The completion stage recorded **13.691 CPU-hours in total**, including the
build and input checks above, development attempts, reviews, portable-tool
controls and final manifest validation. Of that total, **0.686 CPU-hours**
belong to unsuccessful or deliberately rejected transactions. The earlier
pricing investigation is separate: **22.117 CPU-hours**, including
5.827 CPU-hours of unsuccessful or superseded attempts. Component and
latest-successful-module summaries are not added again to these totals.
CPU measures instrumented process transactions, including their monitoring
children; elapsed time and focused agent-hours are different quantities.

Completion used less than its 20–50 CPU-hour planning allocation because the
pricing investigation had already established the classification, transport
and finite-table foundations. The shared six-schedule argument also covers
all twenty A/B prefix layouts, avoiding repeated proofs of the same counter
structure. The earlier investigation's cost remains fully accounted for.

The largest measured compiler peak was **30.84 GB (28.72 GiB)**. Recommended
hardware is approximately **64 GiB RAM for serial checking**, or **128 GiB
for parallel checking with memory-aware admission**. This is practical
guidance based on measured peaks, not a claim that these are minimum RAM
requirements. Several large checks should not be admitted simultaneously
merely because CPU slots are available.

At the final measurement, the portable source/data/check payload occupied
**82.92 MB**, excluding private build directories and caches. Compiled
artifacts are not included in that payload. The retained completion
workspace occupied approximately **3.65 GiB**, including failed attempts,
duplicate outputs and reproduction files. The existing shared Lean and
dependency installation occupied **7.42 GiB separately**. These figures
exclude the separately retained native-search evidence and archive packing.

The measurements are supported by `COMPLETION_COST_SNAPSHOT_FINAL_001.json`
and `COMPLETION_COST_FINAL_ADJUSTMENT_001.json`. The adjustment adds two
terminal receipts that finished after the snapshot, without overlap.
The clean-build custody and joined-binding receipts establish their
respective successful boundaries. No SAT search or certificate replay was
launched during this completion stage.
