# Reproduce the K60 argument

The boundary has **296,797 indexed formulas**: 231,168 E, 56,374 A/B/D, and
9,255 direct entrance/balance cases. Each requires accepted native Kissat
evidence. Lean proves the mathematical reduction, exhaustive coverage and
encoding soundness in `UniformK60.ramsey60_of_exact_unsat`; its explicit premise
is `UniformK60.ExactInputs.AllUnsat`. The large native UNSAT results remain
external evidence, not refutations replayed by the Lean kernel.

## Check the retained evidence

Use Python 3.9+ and the standard library. Obtain the large archives through
Git LFS (`git lfs pull` in a Git checkout). Check the archive hashes against the
independently obtained [release index](publication/checks/K60_RELEASE.json), then
extract into two fresh directories. The archives contain capsule members
directly, without a wrapping directory:

Run these commands from the repository root. The subshell stops on any failed
checksum, directory creation or extraction:

```sh
(
  set -e
  (cd archives && shasum -a 256 -c SHA256SUMS)
  mkdir k60-formal-capsule k60-native-capsule
  tar -xzf archives/k60-formal-evidence.tar.gz -C k60-formal-capsule
  tar -xzf archives/k60-native-evidence.tar.gz -C k60-native-capsule
)
```

Keep the two capsule workspaces separate. Replace the following paths with
your extraction paths, and independently check the printed manifest hashes
against the release index:

```sh
K60_NATIVE=/absolute/path/to/native-capsule
K60_FORMAL=/absolute/path/to/formal-capsule

python3 -B reproduce/native_evidence.py verify \
  --root "$K60_NATIVE" --manifest-sha256 '089599c2c4ed17524bb73727584391f16f85272facaf283d3923e4938f770d95'
python3 -B reproduce/formal_evidence.py verify \
  --root "$K60_FORMAL" --manifest-sha256 '652a69a00fae00c0e49969556e646b1ba2fa223057d2791ef2206ac3e49051a2'
```

These commands launch neither Lean nor a SAT solver and do not execute archived
generator code. Native verification reconstructs the full case/hash census and
checks every retained attempt, command, solver identity, raw log, exit status
and direct UNSAT coverage. Formal verification checks source/import closure,
build and binding records, and the retained complete formula emissions.
Checking those records is separate from rerunning Lean.

Raw records retain their original paths. The manifest maps those paths to
archive members; the original machine and its installed solver are unnecessary.
Keep each capsule unchanged and write new outputs elsewhere. The external
manifest pin is essential; a hash supplied only by the same unchecked payload
is not an independent authentication source.

The [manual evidence workflow](.github/workflows/evidence.yml) runs these same passive
checks using an externally supplied release-index hash. It requires a finalized
local index, downloads only the two K60 archives, and retains the verification
logs. It neither requires publication nor publishes a release, and it does not
rerun Lean or native solvers.

## Build the mathematical source package

The public `formal/` package contains the complete selected source closure and
its classification data. With Python 3.9+, Git and Elan installed, run from the
repository root:

```sh
(
  set -e
  cd formal
  lake exe cache get
  lake env python3 build.py --target UniformK60.Verification --validate-only
  lake env python3 build.py --target UniformK60.Verification --jobs 1
)
```

Keep `formal/lake-manifest.json` unchanged; do not run `lake update`. The builder
checks the pinned toolchain, clean dependency revisions, source hashes and
embedded data, and compiles into a fresh project library. A complete build
replays the 55 small classification certificates but does not rerun the large
native searches. [BUILD.md](formal/BUILD.md) describes the receipts, the small
encoding target and resource scope.

The [push/PR workflow](.github/workflows/verify.yml) audits the complete source
manifest and builds only the five-module `UniformK60.CoreCounts` target. It
does not replay the classification traces or compile the final theorem. The
[manual full-build workflow](.github/workflows/full-lean.yml) uses a provisioned
self-hosted runner for the complete source build and classification replay.
It does not perform exact-input binding or native searches. The corresponding
local targets are `make audit-sources`, `make test-ci`, `make lean-ci` and
`make lean-full`.

For exact comparison with the retained native formulas, use the separate
canonical workflow below. Its source bytes agree with the public package,
while its unchanged build and binding drivers use their recorded layout and
receipt format.

## Rebuild and bind the formal definitions

Use a fresh writable copy of the formal capsule's `workspace/`, preserving its
`k60-lean/`, `k60-pilot/` and `r3333-upper-bound/` sibling layout. Use Python
3.9+, Git, the Lean toolchain named in
`r3333-upper-bound/formal/lean-toolchain`, and clean package checkouts at the
revisions in its `lake-manifest.json`, with their library caches available.
The build checks those revisions and recompiles the selected project closure into a new
library; prior project `.olean` files are not required.

```sh
K60_REBUILD=/absolute/path/to/new-writable-workspace

(
  set -e
  test ! -e "$K60_REBUILD"
  cp -R "$K60_FORMAL/workspace" "$K60_REBUILD"
  python3 -B "$K60_REBUILD/k60-lean/build.py" \
    --target UniformK60.Verification \
    --lean /absolute/path/to/pinned/lean \
    --packages /absolute/path/to/pinned/packages
)
```

After that command succeeds, use its printed `BUILD_RESULT.json` for **all four**
checks, sequentially:

```sh
K60_BUILD_RESULT=/absolute/path/printed/by/the/build/BUILD_RESULT.json

(
  set -e
  python3 -B "$K60_REBUILD/k60-lean/check_base.py" --build-result "$K60_BUILD_RESULT"
  python3 -B "$K60_REBUILD/k60-lean/check_marked_inputs.py" --build-result "$K60_BUILD_RESULT"
  python3 -B "$K60_REBUILD/k60-lean/check_counters.py" --build-result "$K60_BUILD_RESULT"
  python3 -B "$K60_REBUILD/k60-lean/check_balance.py" --build-result "$K60_BUILD_RESULT"
)
```

Stop if any stage fails. The checks bind the shared base, all marked/entrance
formula occurrences, counter clauses, seven balance prefixes and 720 brace
inputs to that same build. They check full input identities, including clause
order and repeated formula occurrences. Retain the printed receipts and logs.
These checks establish formal/input correspondence; they do not run the native
campaigns or discharge the external UNSAT premise.

## Export and rerun an individual formula

The standalone release tool
[`materialize_input.py`](reproduce/materialize_input.py) imports the retained pinned
catalogue code. This is an active reconstruction step, separate from passive
verification above. It needs Python 3.9+ and the retained relative input/code
layout, with no compiler, PySAT or original solver installation.

```sh
python3 -B reproduce/materialize_input.py \
  --workspace "$K60_NATIVE/workspace" --campaign closure \
  --list-ids --prefix C2_ENTRANCE --limit 10

python3 -B reproduce/materialize_input.py \
  --workspace "$K60_NATIVE/workspace" --campaign e \
  --case-id E_TTT_s00000_d12 --output /path/to/new-case.cnf

/path/to/your/kissat /path/to/new-case.cnf > /path/to/new-case.log
```

Campaign choices are `e`, `abd` and `closure`. The destination must be new; the
exporter verifies the complete declared CNF SHA256 before and after writing.
Use your platform's own Kissat for the separate native rerun and retain its
binary/input hashes, command, full log and exit status. Kissat's successful
UNSAT outcome uses exit status 20 and the exact line `s UNSATISFIABLE`; an
individual rerun does not establish coverage of the whole boundary.

The package uses a single Kissat evidence boundary. All 296,797 indexed formulas
require direct native evidence under the documented acceptance checks.
