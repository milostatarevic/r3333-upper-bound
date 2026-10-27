# Reproduction and verification checks

The proof's verification has three parts: the mathematical reduction in
Lean, exact identity between its formulas and native inputs, and the native
UNSAT results. The complete boundary is 56,723 formulas and 113,446 solver
executions. This page identifies the records for each part; executable
commands are in [REPRODUCIBILITY.md](REPRODUCIBILITY.md).

## Mathematics

[`UniformK61.WholeProof.ramsey61`](../formal/src/UniformK61/WholeProof.lean)
proves the bound with the single explicit `AllNativeUnsat` premise over
the concrete formulas. The case count is proved in
`WholeProof.native_case_count`. Coverage, physical vertex and color
transport, the structural balance argument and all host-to-formula
implications are included in the formal reduction.

| Check | Scope and record |
| --- | --- |
| Complete source build | All selected modules, including 32 classification modules and their 55 CNF/LRAT pairs. [Build result](../formal/BUILD_RESULT.json) |
| Source identity | Complete source, embedded data and build-control identities. [Source manifest](../formal/SOURCE_MANIFEST.json) |
| Exact theorem and count | The single native premise and the 56,723-case count, with only the standard axioms `propext`, `Classical.choice` and `Quot.sound`. `math/binding/FINAL_THEOREM_AUDIT.json` in the evidence package |
| Detailed execution | Per-module compiler commands, import identities, output identities, logs and measurements. `math/build/` in the evidence package |

The builder uses the pinned Lean 4.32.1 and external package revisions.
Its project library contains only the current run's compiled outputs.
[Formalization map](FORMALIZATION_STATUS.md) ·
[Classification provenance](CLASSIFICATION_PROVENANCE.md) ·
[Build guide](../formal/BUILD.md)

## Exact input binding

The [binding driver](../formal/reproduce/uniform/README.md) executes the
theorem audit, four Lean emitters and the complete comparison. Its exact
disjoint boundary is 56,374 A/B/D marked cases, 346 direct C entrances and
three full-host balanced cases.

The retained `math/binding/RUN_RESULT.json` identifies the accepted build,
compiler runtime, input catalog and all executed tools. The component
checks compare ordered units, signs, dimensions, byte counts and complete
DIMACS hashes. `math/binding/checks/BINDING_RESULT.json` records the
56,723-case union and its ordered case/hash digest. These are executed
serialization and identity checks, distinct from Lean theorem checking.

## Native evidence

Every required formula has an UNSAT result from Kissat 4.0.4 and CaDiCaL
3.0.1, with default options and no CPU or elapsed-time limit. The
[native verification record](checks/UNIFORM_K61.json) covers all 113,446
executions, with zero SAT, UNKNOWN, error or missing outcomes.

The [release verifier](../reproduce/uniform_release.py) checks each formula's
input identity, raw start/native-start/result records, solver binary,
command, UNSAT log line and native exit code. It checks the exact mapping
between the complete current input catalog and the preserved execution
records. The retained source metadata and local run identifiers are kept
unchanged. These checks do not rerun the solvers or turn their native UNSAT
answers into Lean kernel certificates.

The native cost table is in [MEASURED_COSTS.md](MEASURED_COSTS.md); mathematical
build and binding costs are in [formal/MEASUREMENTS.md](../formal/MEASUREMENTS.md).

## Complete package and routine checks

`archives/evidence-v2.tar.gz` contains `RELEASE.json`, the current inputs,
all required native records and the mathematical execution records above.
The [package verification record](checks/UNIFORM_K61_RELEASE.json) records
verification after extraction into a separate directory. Checksums in
`archives/SHA256SUMS` authenticate the distributed archives.

The release gate requires the current native union, a successful fresh
source build and a matching fresh complete binding before packaging.
The package verifier checks the exact retained file census and all stated
identities using the current repository's verification code. Archived
scripts and binaries are never executed during package verification.

[Push CI](../.github/workflows/verify.yml) checks source/data identities and
small control tests, then builds the five-module physical-encoding target.
Its scope is deliberately separate from the complete proof build and
native searches. The reproducible local checks are listed in the
[Makefile](../Makefile).

The proof standard and its trust boundary are stated in
[TRUST_AND_CERTIFICATION.md](TRUST_AND_CERTIFICATION.md).
