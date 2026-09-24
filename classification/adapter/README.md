# Critical catalogues on the 61-vertex host

[ClassificationAdapter.lean](Ramsey61/ClassificationAdapter.lean) connects
the proved K15/K16 catalogues to the `Ramsey61.Host` type. Every
high monochromatic neighborhood is mapped completely onto a critical
template, preserving actual vertices and one consistent map of the three
remaining colors. It also exposes the K15 extension and the K16 strongly
regular color-graph theorem.

The [check receipt](../build_runs/ADAPTER_FRESH_20260922T073615Z/receipt.json)
and [axiom output](../build_runs/ADAPTER_FRESH_20260922T073615Z/lean.log) record
successful compilation against the 32-module classification closure:
2.30 CPU seconds, 2.89 elapsed seconds and 2,910,715,904 bytes peak RSS.
All seven inspected endpoints use only `propext`, `Classical.choice` and
`Quot.sound`. The source SHA-256 is
`ba4fc9343574e607478103599de47d45f176ba2dfef6cfcea9535f96ab165356`.

[RELOCATION.json](RELOCATION.json) binds the source path used in the check
receipt to this byte-identical packaged file. The same source is included as
[`Ramsey61.ClassificationAdapter`](../../formal/src/Ramsey61/ClassificationAdapter.lean)
in the complete portable build. Its catalogue and physical-neighborhood maps
are used by the formalized K61 case covers and the final Ramsey theorem.

Follow the [complete build instructions](../../formal/BUILD.md) to compile the
adapter together with all its dependencies, including the classification
sources and their 55 CNF/LRAT pairs. The successful
[1,809-module build](../../formal/BUILD_RESULT.json) records that execution.
The [mathematical dependency map](../../formal/MATHEMATICS.md) explains how the
classification endpoints enter the final proof. Push CI separately checks
source integrity and compiles a small encoding target; its scope does not
include compiling this adapter.
