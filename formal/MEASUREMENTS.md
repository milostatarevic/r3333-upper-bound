# Formalization and reproduction measurements

The complete portable mathematical build passed from a fresh checkout with
two compiler workers. It compiled all 1,809 modules, including the 32
classification modules and replay of their 55 small CNF/LRAT pairs. It ran
no SAT search and generated no new refutation certificates.

| Operation | Measured cost | Scope |
|---|---:|---|
| Complete portable build | **9.80 CPU-hours** | Driver and compiler CPU combined; all 1,809 modules |
| Module compilation sum | **9.79 CPU-hours** | Included in the complete-build total, not an additional cost |
| Build elapsed time | **4h58m** | Two compiler workers |
| Separate exact-input check | **142.98 CPU-seconds** | All 56,830 formula identities; not rerun as part of the portable build |

The [build result](BUILD_RESULT.json) records exact measurements and the
compiler, source and dependency identities. The separate
[input-binding record](checks/joined_bindings/RUN_RESULT.json) supplies the
input-check timing. Native SAT search costs are given in the
[search cost table](../publication/MEASURED_COSTS.md).

The peak single compiler used **28.78 GiB RSS**. The sampled peak across
concurrent compiler processes was **37.7 GiB**. These measurements support a
recommendation of **64 GiB RAM for serial checking**, or **128 GiB for
controlled parallel checking**. The portable builder's job count is a fixed
concurrency ceiling, not an adaptive memory controller; sampled peaks are
not guarantees for another run.

The build workspace used **4.21 GiB** of allocated disk space, and the
pinned dependencies used **7.34 GiB**. The fresh checkout occupied
**11.67 GiB in total**, excluding the native-search evidence archive.
One copy of the compiled `.olean` files contained **2.25 GB** of logical data;
the build workspace also retains logs, receipts and other compiler outputs.
Allow approximately **12 GiB for the checkout, dependencies and build**,
in addition to space for the separate evidence archive and its extraction.
