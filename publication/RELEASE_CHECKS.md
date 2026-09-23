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
| Independent D base specification | PASS: all 12 owner/component bases through 18 exact-byte comparisons, including all 42 five-row counter blocks; 4.83 CPU seconds. Excludes per-leaf suffixes and finite-cover proofs | [Specification check](checks/D_BASE_CHECK.json), [checker](../reproduce/d_base_check.py) |
| C input reconstruction | PASS: all 456 exact formula hashes; 0.24 CPU seconds without writing repeated base clauses | [All C inputs](../reproduce/checks/ALL_C_INPUTS_001.json) |
| Finite G replay | PASS: the 72-state local relation and 3,600 + 10,368 checked contradictions; 2.18 CPU seconds | [Execution receipt](../reproduce/checks/G_REPLAY_001/REPLAY_RECEIPT.json) |
| Verifier failure paths | PASS: 23 archive/C and 10 A/B/D synthetic tests reject corrupted inputs or censuses and unsafe paths | [Archive/C tests](../reproduce/test_verify.py), [A/B/D tests](../reproduce/test_abd_inputs.py) |
| Clean-checkout reproduction | PASS: portable archive, input and finite-check tools from a local clone without hardlinks | [Clean-checkout receipt](checks/CLEAN_CHECKOUT_001.json) |

These checks authenticate and reproduce the evidence within their stated
scope. Input hashes establish formula identity; the native UNSAT records
supply the search results. Reconstructing a formula does not run its solver.
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
| Clean mathematical build | 1,777 modules compiled and 32 pinned classification outputs reused; 12.263 CPU-hours, 2h31m23s compiler span. [Source/import/output custody](../formal/checks/clean_build/CLEAN_BUILD_CUSTODY.json) |
| Final theorem and exact count | The theorem has only `AllNativeUnsat` over 56,830 concrete CNFs; standard axioms only. [Theorem and build record](../formal/VERIFICATION.md) |
| Complete clean-output input binding | All 56,830 input identities match; 142.98 CPU-seconds, no solver calls. [Joined binding record](../formal/checks/joined_bindings/RUN_RESULT.json) |
| Mathematical source package | Source, embedded data and build tools; no compiled artifacts. [Package file manifest](../formal/PACKAGE_FILES.json), [build identity](../formal/BUILD_IDENTITY.json) |

[VERIFICATION.md](../formal/VERIFICATION.md) explains the custody and theorem
checks. [MEASUREMENTS.md](../formal/MEASUREMENTS.md) distinguishes mathematical
build cost, development cost, memory and storage. Routine CI compares the
mathematical source against its [build identity](../formal/BUILD_IDENTITY.json)
before the compact Lean build. The
[hosted Actions check](https://github.com/milostatarevic/ramsey61-provisional-staging/actions/runs/35819483295)
passed on commit `e6a721ad3b8cc3399e418c75f69da7b3143aa967`, including
source-integrity controls and the compact target.

| Check | Result and scope | Evidence |
| --- | --- | --- |
| K15/K16 classification | All 32 packaged source modules and 55 CNF/LRAT pairs were rebuilt without the original project's compiled objects; 827.71 CPU seconds | [Classification replay](../classification/build_runs/20260922T072158Z_1790061718513440000/SUMMARY.json) |
| Deterministic C-base identity | All 1,880,888 clauses emitted from Lean match the archived base byte for byte, including DIMACS header | [Binding tools and receipts](checks/C_BASE_BINDING_001/README.md) |
| Complete mathematical source and data | The manifest identifies the proof sources, embedded classification data, dependency pins and build controls | [Source manifest](../formal/SOURCE_MANIFEST.json) |

The local clean mathematical build reuses 32 pinned, previously checked
classification outputs. The portable full-source command includes replay of
their 55 small CNF/LRAT pairs. Its supplied execution receipts cover the
compact target, not yet the full source closure. The full local build and
separate classification replay have the scopes shown above; the local build's
Mathlib artifact-provenance limits are described in
[VERIFICATION.md](../formal/VERIFICATION.md). These classification traces are
distinct from the large native SAT searches used by the final theorem.

Exact formula-to-input bindings are checked by the external
[reproduction tools](../formal/reproduce/README.md). They connect the
Lean-defined formulas to the recorded solver inputs. The native results
supply UNSAT evidence; mathematical compilation and byte comparison do not
rerun those searches.

Routine push CI checks all manifested mathematical-source and embedded-data identities, source policy and
reproduction controls, and compiles the five-module coloring-encoding target.
Its uploaded receipts describe that scope. The [full mathematical build](../formal/BUILD.md)
is a separate operation with higher RAM requirements.

## Repository checks

A limited [credential-pattern screen](checks/ARCHIVE_CREDENTIAL_SCREEN_001.json)
found no matches for its specified high-confidence patterns in the archive.
Its receipt defines the screen; it makes no broader claim about redistribution
rights or every possible sensitive string.
