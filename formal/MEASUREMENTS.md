# Formalization and reproduction measurements

The complete mathematical build used **12.89 compiler CPU-hours and 3 hours 1 minute elapsed**, with 8 compiler workers. The exact input binding
then used **531 seconds of CPU and 531 seconds elapsed time**. These measurements
are for the accepted 857-module source build and its 56,723-formula binding
on an Apple M4 Max with 128 GiB RAM. Neither operation launches a SAT search.
Native search costs are reported [separately](../publication/MEASURED_COSTS.md).

## Computation and memory

| Operation | CPU time | Elapsed time | Largest recorded process RSS |
|---|---:|---:|---:|
| Complete Lean source build, 8 workers | 12.89 hours | 3 hours 1 minute | 21.93 GiB |
| Exact input binding | 531 seconds | 531 seconds | 2.80 GiB |

The build CPU total sums the 857 compiler receipts and excludes coordinator
overhead. Its elapsed interval is recorded in
[`BUILD_RESULT.json`](BUILD_RESULT.json). The binding total includes its
driver and custody checks, theorem audit, four Lean emitters and joined
comparison. The six child commands account for 520 CPU-seconds within that
total; their time is not added again.

These RSS figures are individual-process peaks, not simultaneous machine
memory or minimum RAM requirements. Concurrent compilers, the operating
system and other applications need additional memory. The builder's `--jobs`
option sets the maximum number of compiler processes; each compiler uses
one worker thread. CPU totals and elapsed time therefore measure different
things and should not be used interchangeably.

The release package retains the detailed compiler receipts under
`math/build/` and the binding's `RUN_RESULT.json` and execution logs under
`math/binding/`. They identify the source, runtime and measurement scope.

## Observed storage

| Artifact | File-content bytes | Approximate size |
|---|---:|---:|
| Complete fresh build directory, including artifacts and receipts | 1,439,534,589 | 1.34 GiB |
| Accepted project library, included in the build directory above | 718,173,480 | 0.67 GiB |
| Binding outputs, comparisons and receipts | 190,199,997 | 181.39 MiB |
| Complete generated native input directory | 50,401,787 | 48.07 MiB |

These are measured file-content sizes, not capacity requirements. The
filesystem reported 1.35 GiB of allocated file blocks for the build,
183.88 MiB for the binding directory and 48.08 MiB for generated inputs.
Allocation depends on the filesystem. These figures exclude the external
Lean/Mathlib dependency caches, native solver records and compressed release
archive. Reproduction also needs working space for the chosen operation;
archive extraction requires separate space from the archive itself.

The build directory keeps both per-module compiler outputs and the accepted
project library. The binding stores the shared base and compact signed unit
tables for 56,720 marked cases, plus the three balanced formulas in full.
Their identities are compared without materializing every complete marked
CNF. The release archive retains native evidence and mathematical execution
records; it does not distribute the compiled project library or bulk binding
emissions. Its exact compressed size is recorded in
[the release acceptance receipt](../publication/checks/UNIFORM_K61_RELEASE.json).

## Fixed verification scope

| Scope | Size |
|---|---:|
| Lean project source closure | 857 modules |
| Embedded classification data | 110 files, comprising 55 CNF/LRAT pairs |
| Final formulas | 56,723 |
| Required native solver runs | 113,446 |
| Shared physical base | 7,320 variables; 156,770 clauses |
| Each balanced formula | 13,656 variables; 524,462 clauses |
| Three balanced DIMACS files | 40,567,176 bytes |

The [build guide](BUILD.md), [binding guide](reproduce/uniform/README.md) and
[repository reproduction guide](../publication/REPRODUCIBILITY.md) give the
commands for these distinct operations.
