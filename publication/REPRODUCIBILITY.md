# Reproduce the proof computations

The tools below authenticate the evidence archive, reconstruct every SAT
input used by the proof, and rerun the independent finite G checks. They use
Python 3.9 or later and its standard library. Run the commands from the
repository root. SAT reruns require a separately installed solver. The full
Lean build uses Python 3.10 or newer and the pinned toolchain described in
[formal/BUILD.md](../formal/BUILD.md).

The proof uses **56,830 distinct SAT formulas**: 56,374 in the A/B/D families
and 456 full-host C formulas. The C results were checked with both Kissat and
CaDiCaL. Another 13,968 G configurations are excluded by direct finite checks.
[Measured search costs](MEASURED_COSTS.md) give detailed search and
verification phase accounting.

## 1. Obtain and authenticate the evidence

Fetch `archives/evidence-v1.tar.gz` with Git LFS, or provide an offline copy.
The verifier detects an unexpanded LFS pointer and performs no download.

```sh
python3 -B reproduce/verify.py check
```

For an offline copy, add `--archive /path/to/evidence-v1.tar.gz`. The archive
has 375,104,364 bytes and SHA256
`2b85cac94df0317a532aa823cfea93ac83738093fc854805896943f90d468757`.
This command authenticates the compressed bytes; the next command checks the
contents and their recorded relationships.

## 2. Extract and verify the complete evidence

The extractor requires a 100 GiB free-space floor plus an 8 GiB extraction
reserve. It bounds logical extraction to 4 GiB and one million members; actual
filesystem allocation depends on the number and size of small files. Choose
a work directory on a filesystem meeting these requirements.

```sh
proof_work_dir=$(mktemp -d)
python3 -B reproduce/verify.py full \
  --extract-to "$proof_work_dir/snapshot" \
  --receipt "$proof_work_dir/verification.json"
```

The destination and receipt must not already exist, and the receipt must be
outside the extracted snapshot. Add `--archive /path/to/evidence-v1.tar.gz`
when using an offline archive. The archive is authenticated before extraction;
unsafe paths, duplicate members, links and special files are rejected.

Successful verification establishes that:

- All **455,901 payload files**, totaling **2,078,952,544 bytes**, match the
  manifest, with no missing or additional files.
- Input, generator, result, log and source-reference hashes agree with the
  complete evidence census.
- Every one of the 456 C inputs is linked to matching accepted UNSAT answers
  from both native solvers on the same complete formula hash.
- The mathematical dependency and computation records agree with the
  supplied result manifest.

The snapshot is read-only input to subsequent checks. Keep receipts, generated
CNFs, solver logs and other output outside it; adding even a `.DS_Store` file
invalidates the exact census. Absolute paths inside archived records identify
source provenance and are resolved through the included source map, not opened
on the reader's machine. Partial output from an unsuccessful check is retained
for inspection and is not accepted as verified evidence.

A reference run used about 213 combined CPU seconds for extraction and full
verification. Receipts are supplied under `reproduce/checks/`; this timing is
separate from SAT search costs.

## 3. Verify and reconstruct C inputs

The input and receipt writers retain the 100 GiB free-space floor, including
hash-only checks that write only a small receipt. Use the work filesystem
selected in Section 2 for Sections 3–4.

Check all 456 complete C formula hashes without writing 18.06 GB of repeated
formula bodies:

```sh
python3 -B reproduce/verify.py verify-c-all \
  --snapshot "$proof_work_dir/snapshot" \
  --receipt "$proof_work_dir/c-input-verification.json"
```

To write one exact formula, choose a case from `R3_000` through `R3_455`:

```sh
python3 -B reproduce/verify.py materialize-c \
  --snapshot "$proof_work_dir/snapshot" --case R3_000 \
  --output "$proof_work_dir/R3_000.cnf" \
  --receipt "$proof_work_dir/R3_000.json"
```

Each formula consists of the pinned `BROAD_BASE_001.cnf` body and the signed
physical units from its row of `SEEDS.json`, with the corresponding DIMACS
header. The tool verifies the complete output hash and rereads the written
file. It uses the base and seed data required by the proof, independently of
labels in archived metadata.

For example, `R3_000` has 39,607,141 bytes, 439,723 variables and 1,881,332
clauses. Its SHA256 is
`b56b6f042afd2b5e5eb70acf679c75cf9027fa20bb135016eca73559462724c9`.
The all-input hash check used 0.240 CPU seconds in the reference run.
Neither command invokes a solver.

## 4. Verify and reconstruct A/B/D inputs

Check the complete A/B/D formula boundary without materializing its repeated
input bodies:

```sh
python3 -B reproduce/abd_inputs.py verify-all \
  --snapshot "$proof_work_dir/snapshot" \
  --receipt "$proof_work_dir/abd-input-verification.json"
```

| Family option | Distinct formulas |
|---|---:|
| `A` | 360 |
| `B` | 5,096 |
| `D_UUU` | 679 |
| `D_UUT` | 679 |
| `D_UTU` | 6,576 |
| `D_UTT` | 6,576 |
| `D_TTU` | 18,204 |
| `D_TTT` | 18,204 |
| **Total** | **56,374** |

List the case identifiers for a family and materialize a chosen formula:

```sh
python3 -B reproduce/abd_inputs.py list \
  --snapshot "$proof_work_dir/snapshot" --family D_UUU
python3 -B reproduce/abd_inputs.py materialize \
  --snapshot "$proof_work_dir/snapshot" --family D_UUU \
  --case ACTUAL_CASE_ID_FROM_LIST \
  --output "$proof_work_dir/chosen-D_UUU.cnf" \
  --receipt "$proof_work_dir/chosen-D_UUU.json"
```

The adapter reconstructs exact shared prefixes, variable maps and suffixes,
and compares each complete formula with its recorded input hash. Outputs must
be new files outside the snapshot. The all-input check used 3.70 CPU seconds
in the reference run; this measures input verification, not solving.

Full per-case A/B/D CNFs are not archived. Their reconstruction is checked
against runner-recorded input hashes. The
[A/B/D evidence index](ABD_EVIDENCE_INDEX.md) lists the complete manifests,
finite tables and reconstruction assets, including their exact hashes.

### Join every A/B/D formula to its native UNSAT record

The native-result audit reconstructs all 56,374 formula hashes and joins them
to authenticated result, claim and log records. It checks exact case IDs,
formula dimensions, UNSAT status and solver exit 20, including adopted
mixed-D results and the retained UUT pilot. It invokes no solver and writes
no complete CNFs.

```sh
python3 -B reproduce/abd_native.py \
  --snapshot "$proof_work_dir/snapshot" \
  --receipt "$proof_work_dir/abd-native.json"
```

The receipt must be a new file outside the authenticated snapshot. The
checker verifies recorded evidence; it does not establish solver correctness
or replace a fresh SAT run.

### Check the D base specification independently

The following checker re-emits the clause specification in
[D cover and encoding](D_COVER_AND_ENCODING.md), without importing the
campaign generators, and compares it with the retained base bytes:

```sh
python3 -B reproduce/d_base_check.py \
  --snapshot "$proof_work_dir/snapshot" \
  --receipt "$proof_work_dir/d-base-specification.json"
```

It checks all 12 owner/component bases through 18 sparse-base or dense-prefix
comparisons, including all good-coloring clauses, template units and 42
five-row counter blocks. The recorded run used 4.83 CPU seconds. It checks
neither the finite support/matrix cover nor the per-leaf suffixes or UNSAT
answers; those obligations have their own arguments and checks. The receipt
must be a new file outside the authenticated snapshot.

## 5. Replay the local relation and G exclusions

```sh
python3 -B reproduce/g_check.py \
  --snapshot "$proof_work_dir/snapshot" \
  --output "$proof_work_dir/g-replay"
```

The output directory must not already exist. The adapter executes the pinned
independent finite checkers with their exact inputs and writes source, input
and result hashes to `REPLAY_RECEIPT.json`. It writes nothing inside the
snapshot and invokes no SAT solver.

The checks establish:

- The local equations have rank 65 and nullity 15; enumeration of all 32,768
  free-coordinate sign assignments recovers exactly 72 states.
- Every one of the 3,600 isomorphic-map G labels and 10,368 complementary G
  labels is rejected by its physical witness check.
- Both checker control suites pass, with 11 and 19 controls respectively.

A reference run used 2.177987 CPU seconds and 40,386,560 bytes peak RSS.
The adapter has a 60 CPU-second ceiling, a 64 MiB output-tree bound and the
100 GiB disk floor. Exact receipts are in `reproduce/checks/G_REPLAY_001/`.
The physical guard and exhaustive host-to-label arguments are proved in the
[Lean development](../formal/MATHEMATICS.md) and explained in
[proof.md](../proof.md). The Python replay is a separate execution of the
retained finite checks.

## 6. Rerun the SAT searches

After materializing and hash-checking a CNF, run a locally installed solver
on that exact file. For example:

```sh
solver_binary=/absolute/path/to/kissat
solver_status=0
"$solver_binary" "$proof_work_dir/R3_000.cnf" \
  > "$proof_work_dir/R3_000.solver.log" 2>&1 || solver_status=$?
printf '%s\n' "$solver_status" > "$proof_work_dir/R3_000.solver.exit"
test "$solver_status" -eq 20
```

Inspect the complete log for its UNSAT result as well as the exit status.
Kissat and CaDiCaL conventionally return 20 for UNSAT. A failure, cap or UNKNOWN
answer provides no exclusion. Use resource limits appropriate to the host and
a new output basename for each attempt.

Retain the command, complete input hash, solver version and binary hash, log,
exit status and measured cost. The recorded solvers are Kissat 4.0.4 and
CaDiCaL 3.0.1. A build for another platform can have a different binary hash;
record its identity with the new results.

To repeat all required SAT computations, enumerate every ID in the eight
A/B/D families and all 456 C IDs. Run both solvers for C to reproduce its
two-solver check. The total is 56,830 distinct formulas; the second solver
for C adds runs, not new formulas. The separate G computations are covered
by Section 5.

## 7. Build the Lean mathematical reduction

The [formal package](../formal/README.md) proves the reduction to all 56,830
concrete CNFs. Its main theorem has only the computational premise
`AllNativeUnsat`; case coverage, transport and encoding soundness are proved.
The pinned setup and complete instructions are in [BUILD.md](../formal/BUILD.md).
From the repository root:

```sh
(
  cd formal
  lake exe cache get
  lake build Mathlib.Combinatorics.SimpleGraph.Bipartite
  lake env python3 build.py --validate-only
  lake env python3 build.py --jobs 1
)
```

Keep the supplied `lake-manifest.json`; do not run `lake update`. The compiler
must match `lean-toolchain` (Lean 4.32.1), and the builder checks the locked
external dependency revisions. The default build includes the classification
sources and replays their **55 supplied small CNF/LRAT pairs**. It runs no SAT
search. The recorded clean mathematical validation used local controllers
and reused 32 pinned classification outputs, whose separate kernel-replay
provenance is described in
[CLASSIFICATION_PROVENANCE.md](CLASSIFICATION_PROVENANCE.md). The portable
builder has a recorded five-module CI execution; a complete portable run is
not included in the supplied build receipts. [VERIFICATION.md](../formal/VERIFICATION.md)
distinguishes the recorded build and dependency provenance.

For planning, use a **64 GiB host with one compiler**. A 128 GiB host supports
controlled parallel work with admissions adjusted to actual memory pressure;
it does not make eight simultaneous heavy compilers safe by default. A
measured single compiler peaked at **28.72 GiB RSS**. The portable `--jobs`
option is a concurrency ceiling, not an adaptive memory controller. Start at
one and select higher concurrency only for the available memory. The measured
peak is not a bound on aggregate machine memory or future runs.

Each invocation creates a fresh `.build/runs/<timestamp>_<id>/` directory,
with an isolated `lib/` namespace, immutable module receipts and a final
`BUILD_RESULT.json`. A successful complete build, including its binding
helpers, provides the library used in Section 8. Source validation alone is
not a proof build.

### Routine CI

Routine CI checks all manifested mathematical sources and embedded data and
compiles the five-module dependency closure of
`PricingIntegration.NativeColoringClauses`. Its compilation command is:

```sh
(
  cd formal
  lake env python3 build.py --target PricingIntegration.NativeColoringClauses \
    --no-certificate-replay --jobs 1
)
```

This bounded target is separate from the full mathematical build. It performs
no classification certificate replay or native SAT search and does not compile
the final theorem. The no-replay flag rejects a selected dependency closure
containing a certificate command instead of silently skipping that source.

## 8. Bind the Lean formulas to the native inputs

The tools in [formal/reproduce/README.md](../formal/reproduce/README.md) emit
and compare the concrete formulas from a successful complete Lean build.
They use its explicit isolated `lib/` path; plain `lake build` is not this
package's mathematical build entry point.

The shared D emitter produces twelve prefix bodies. The common-family check
binds **55,016** A/B/mixed-D inputs, the UUU/UUT check binds **1,358**, and the
[C check](../formal/reproduce/c/README.md) binds the remaining **456**. Together
they verify complete input identities for the theorem's 56,830-case boundary,
including headers, variables, clause counts, literal signs and ordering.
Use fresh output directories outside the authenticated evidence snapshot.

These external byte comparisons connect Lean definitions with retained or
reconstructed formula bytes; the input and result checks match their SHA-256
values to runner-recorded input hashes. They run no SAT solver and do not turn native UNSAT answers
into kernel-checked refutation certificates. The archive and native-result
checks in Sections 1–6 retain their separate roles.

## Scope and tool tests

Archive authentication and formula reconstruction establish data identity;
independent solver runs establish native UNSAT answers. The Lean proof
establishes the physical reductions, exhaustive case covers and concrete
encoding implications under `AllNativeUnsat`; external binding
checks connect those formulas to the native evidence. Together these are the
verification components of the computer-assisted proof.
The commands above reconstruct the proof inputs without recreating a
particular research machine or its campaign controllers.

The small synthetic tests exercise rejection of tampered hashes and censuses,
unsafe archive paths, invalid units, corrupt suffixes and incorrect outputs:

```sh
python3 -B reproduce/test_verify.py
python3 -B reproduce/test_abd_inputs.py
```

They create temporary fixtures and do not alter the evidence or run a search.
