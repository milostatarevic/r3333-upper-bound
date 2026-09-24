# Reproduction and verification checks

This page indexes checks of the supplied evidence, input reconstruction,
finite computations and Lean mathematical proof. Each receipt states
what was checked and identifies the files used. The mathematical argument is
in [proof.md](../proof.md); the trust boundary is described in
[TRUST_AND_CERTIFICATION.md](TRUST_AND_CERTIFICATION.md).

## Computational evidence and reproduction

| Check | Result and scope | Receipt |
| --- | --- | --- |
| Archive extraction and verification | PASS: 455,901 payload files, 2,078,952,544 bytes and recorded C/final evidence relationships; about 213 combined driver/checker CPU seconds | [Archive verification](checks/ARCHIVE_FULL_VERIFICATION_001.json) |
| A/B/D input reconstruction | PASS: all 56,374 exact formula hashes; 3.70 CPU seconds on extracted evidence | [All A/B/D inputs](checks/ABD_ALL_INPUTS_001.json) |
| A/B/D file materialization | PASS: 56 representatives covering every distinct prefix/family; all persisted files rehashed | [Materialization check](checks/ABD_MATERIALIZATION_001.json) |
| Original A/B/D Kissat input/result identities | PASS: all 56,374 reconstructed formulas match their original accepted Kissat UNSAT records | [Verification receipt](checks/ABD_NATIVE.json), [checker](../reproduce/abd_native.py) |
| A/B/D CaDiCaL input/result identities | PASS: all 56,374 reconstructed formulas match accepted CaDiCaL 3.0.1 UNSAT records; zero SAT, UNKNOWN or error results. The campaign used 246.814166 native solver CPU hours | [Verification receipt](checks/ABD_SECOND_SOLVER_VERIFICATION.json), [checker](../reproduce/abd_second_solver.py), [campaign summary](checks/ABD_SECOND_SOLVER.json) |
| Independent D base specification | PASS: all 12 owner/component bases through 18 exact-byte comparisons, including all 42 five-row counter blocks; 4.83 CPU seconds. Excludes per-leaf suffixes and finite-cover proofs | [Specification check](checks/D_BASE_CHECK.json), [checker](../reproduce/d_base_check.py) |
| C input reconstruction | PASS: all 456 exact formula hashes; 0.24 CPU seconds without writing repeated base clauses | [All C inputs](../reproduce/checks/ALL_C_INPUTS_001.json) |
| Finite G replay | PASS: the 72-state local relation and 3,600 + 10,368 checked contradictions; 2.18 CPU seconds | [Execution receipt](../reproduce/checks/G_REPLAY_001/REPLAY_RECEIPT.json) |
| Reproduction and source-policy tests | PASS: 112 tests cover archive/C verification, A/B/D inputs, both native-result checkers and Lean source/build audits | [Test commands](../Makefile), [published CI run](https://github.com/milostatarevic/r3333-upper-bound/actions/runs/36041076604) |

These checks authenticate and reproduce the evidence within their stated
scope. Input hashes establish formula identity; the native UNSAT records
supply the search results. All 56,830 main SAT formulas have matching Kissat
and CaDiCaL UNSAT results; the C reconciliation is included in the original
archive, and the A/B/D rerun in `archives/abd-cadical.tar.gz`.
Reconstructing a formula does not run its solver.
Commands for a fresh search are in [REPRODUCIBILITY.md](REPRODUCIBILITY.md).

## Lean mathematics and exact input bindings

The [Lean package](../formal/README.md) proves the complete mathematical
reduction to 56,830 concrete CNFs. Its theorem
[`NativeWholeProof.ramsey61`](../formal/src/PricingIntegration/NativeWholeProof.lean)
takes only `AllNativeUnsat` as an explicit computational premise. The
[source manifest](../formal/SOURCE_MANIFEST.json) pins every mathematical
source and embedded data file. The [formalization map](FORMALIZATION_STATUS.md)
identifies the component theorems and exact scope.

| Complete mathematical check | Result and evidence |
| --- | --- |
| Complete portable mathematical build | All 1,809 modules compiled from a fresh checkout, including 32 classification modules and 55 CNF/LRAT pairs; 9.80 CPU-hours, 4h58m with two workers. [Build result](../formal/BUILD_RESULT.json) |
| Final theorem and exact count | The theorem has only `AllNativeUnsat` over 56,830 concrete CNFs; standard axioms only. [Theorem and build record](../formal/VERIFICATION.md) |
| Separate complete input binding | All 56,830 input identities match using the complete portable build's library; no solver calls. The receipt pins the same source manifest as the build. [Joined binding record](../formal/checks/joined_bindings/RUN_RESULT.json) |
| Mathematical source package | Source, embedded data and build tools; no compiled artifacts. [Package file manifest](../formal/PACKAGE_FILES.json), [build result](../formal/BUILD_RESULT.json) |

[VERIFICATION.md](../formal/VERIFICATION.md) explains the custody and theorem
checks. [MEASUREMENTS.md](../formal/MEASUREMENTS.md) distinguishes mathematical
build cost, memory and storage. Routine CI checks the mathematical source
against the manifest accepted by the full build before compiling the compact
Lean target.

| Check | Result and scope | Evidence |
| --- | --- | --- |
| K15/K16 classification | All 32 current source modules were compiled and all 55 CNF/LRAT pairs replayed within the complete portable build, using source manifest `15b6775769f3578acd5c6aa22c46506decb3c041bd98912a79d50dd6e55ea8ed` and no reused project artifacts | [Complete build record](../formal/BUILD_RESULT.json), [classification provenance](CLASSIFICATION_PROVENANCE.md) |
| Deterministic C-base identity | All 1,880,888 clauses emitted from Lean match the archived base byte for byte, including DIMACS header | [Binding tools and receipts](checks/C_BASE_BINDING_001/README.md) |
| Complete mathematical source and data | The manifest identifies the proof sources, embedded classification data, dependency pins and build controls | [Source manifest](../formal/SOURCE_MANIFEST.json) |

The full build records Lean 4.32.1, the nine pinned external package revisions
and imported-artifact hashes. Its isolated project library contains only
outputs produced by that run. The classification traces are checked inside
Lean; the large native SAT searches retain the separate scope described in
[VERIFICATION.md](../formal/VERIFICATION.md).

Exact formula-to-input bindings are checked by the external
[reproduction tools](../formal/reproduce/README.md). They connect the
Lean-defined formulas to the recorded solver inputs. The native results
supply UNSAT evidence; mathematical compilation and byte comparison do not
rerun those searches.

Routine push CI checks all manifested mathematical-source and embedded-data identities, source policy and
reproduction controls, and compiles the five-module coloring-encoding target.
The [published run for commit ee5ab01](https://github.com/milostatarevic/r3333-upper-bound/actions/runs/36041076604)
passed and retains receipts describing that scope. The [full mathematical build](../formal/BUILD.md)
is a separate operation with higher RAM requirements.

## Repository checks

A limited [credential-pattern screen](checks/ARCHIVE_CREDENTIAL_SCREEN_001.json)
found no matches for its specified high-confidence patterns in the archive.
Its receipt defines the screen; it makes no broader claim about redistribution
rights or every possible sensitive string.
